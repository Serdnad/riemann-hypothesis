module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem theta_Z_mem_range_iC {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) (t : A3.fam3.base3.Tup) :
    ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R t).ZHg A3.A.fam.X := hIB.1 t hz
  obtain ⟨x, hx⟩ := GlobalTheory.PrincipalRows.mem_range_toF_full (A3.A.fam.R t) A3.A.fam.X (X.zs.Z t) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ t (X.jR t y)) hx



theorem iC_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC hUp hRT hIB t
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := GlobalTheory.PrincipalRows.theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT t
    (LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t))
    (theta_Z_mem_range_iC A3 (R.toCx3 F) hIB t)
  have hinj : Function.Injective (LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    show Function.Injective (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)))
    rw [Tw.adjoint_map]
    intro x y hxy
    exact hUp t hxy
  have hinj2 : Function.Injective ((R.toCx3 F).Θ t ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have h0 : LinearMap.adjoint ((R.toCx3 F).Θ t) e = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_left]
      have : (R.toCx3 F).Θ t (LinearMap.adjoint ((R.toCx3 F).Θ t) e) = 0 := he
      rw [this, inner_zero_right]
    exact hinj (h0.trans (map_zero _).symm)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj2
  rw [eq_top_iff]
  intro e _
  obtain ⟨e', rfl⟩ := hsurj e
  exact hmem e'

end GlobalTheory.PrimIn
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conj_torsionTranslateCombination_entire_gaussianGrowth : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  first | exact @GlobalTheory.ConjComb.conj_pres | exact GlobalTheory.ConjComb.conj_pres | (intros; apply GlobalTheory.ConjComb.conj_pres <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_cofinite  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_lattice_principal_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  intro L _ _ κ ℓ
  obtain ⟨S₁, hS₁⟩ := isIntB_mul_star_eventually L
    (RingHom.toOpposite (RingHom.id L) fun x y => mul_comm x y) κ ℓ
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple L κ ℓ
  refine ⟨S₁ ∪ S₂, fun v hv I h0 hadd hmul ⟨D, hD0, hDI, hIO⟩ => ?_⟩
  have hv₁ : v ∉ S₁ := fun h => hv (Finset.mem_union_left _ h)
  have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
  have hOmul := (hS₁ v hv₁).1
  have hloc := hS₂ v hv₂
  have hOadd : ∀ y z, IsIntB v ℓ y → IsIntB v ℓ z → IsIntB v ℓ (y + z) := fun y z hy hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy i) (hz i)
  have hone : (1 : ℤ) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hloc1 : ∀ c : ℤ, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * (c : L)) := fun c =>
    ⟨1, hone, by rw [Int.cast_one, one_mul, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap⟩
  have hcast : ∀ c : ℤ, ((c : v.adicCompletion ℚ ⊗[ℚ] L)) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (c : L) :=
    fun c => by rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
  have hO : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) →
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := fun c hc => (hloc c).2 hc
  have htm : ∀ a b : L, ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b) =
      (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a * b) := fun a b => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hDL : (D : L) ≠ 0 := Int.cast_ne_zero.2 hD0
  let K : Set L := {a | (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a / D) ∈ I}
  have hK0 : (0 : L) ∈ K := by
    show _ ∈ I; rw [zero_div, TensorProduct.tmul_zero]; exact h0
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := fun a ha b hb => by
    show _ ∈ I; rw [add_div, TensorProduct.tmul_add]; exact hadd _ ha _ hb
  have hKmul : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K :=
    fun c hc a ha => by
      show _ ∈ I; rw [mul_div_assoc, ← htm]; exact hmul _ (hO c hc) _ ha
  have hKloc : ∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a) := fun a ha => by
    apply (hloc a).1
    have := hIO _ ha
    rwa [hcast, htm, mul_div_cancel₀ _ hDL] at this
  obtain ⟨g, hgK, hg⟩ := GlobalTheory.T.exists_generator_localized_integers_ideal_in_field L v K hK0 hKadd hKmul hKloc
  have hDK : (D : L) * D ∈ K := by
    show _ ∈ I
    have h1 := hDI _ (hO _ (hloc1 1))
    rwa [Int.cast_one, ← Algebra.TensorProduct.one_def, mul_one, hcast,
      ← mul_div_cancel_right₀ (D : L) hDL] at h1
  obtain ⟨c₀, hc₀, hc₀g⟩ := hg _ hDK
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc₀g; exact hDL (mul_self_eq_zero.1 hc₀g)
  have e1 : g / D * (D / g) = 1 := by field_simp
  have e1' : D / g * (g / D) = 1 := by field_simp
  let m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    { val := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D), inv := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (D / g),
      val_inv := by rw [htm, e1]; rfl
      inv_val := by rw [htm, e1']; rfl }
  refine ⟨m, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, ρ₁, hρ₁, rfl⟩ := GlobalTheory.T.adicTensor_exists_rational_add_integral_mul L κ ℓ v x D hD0
    have hy : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y ∈ I := by
      have h2 : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ((-1 : ℤ) : L) * ((D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ₁) ∈ I :=
        hmul _ (hO _ (hloc1 _)) _ (hDI _ hρ₁)
      have := hadd _ hx _ h2
      convert this using 1
      rw [← hcast]; push_cast; ring
    have hyK : (D : L) * y ∈ K := by
      show _ ∈ I; rwa [mul_div_cancel_left₀ _ hDL]
    obtain ⟨c, hc, hcg⟩ := hg _ hyK
    have e2 : g / D * c = y := by
      rw [div_mul_eq_mul_div, mul_comm g c, ← hcg, mul_div_cancel_left₀ _ hDL]
    have e3 : g / D * c₀ = D := by
      rw [div_mul_eq_mul_div, mul_comm g c₀, ← hc₀g, mul_div_cancel_left₀ _ hDL]
    refine ⟨(1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c + (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c₀ * ρ₁,
      hOadd _ _ (hO c hc) (hOmul _ _ (hO c₀ hc₀) hρ₁), ?_⟩
    show _ = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D) * _
    rw [mul_add, htm, ← mul_assoc, htm, e2, e3, hcast]
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mul_comm]
    exact hmul ρ hρ _ hgK

end GlobalTheory.AdicSpan
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped MonObj

namespace GlobalTheory.PtDeg.FrameExact
open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

section
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

lemma comb_add' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c c' : Fin n → R) :
    comb v (c + c') = comb v c * comb v c' :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_add hv
    ((isLieComb_iff_comb _ _ _).2 rfl) ((isLieComb_iff_comb _ _ _).2 rfl))).symm

lemma comb_zero' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    comb v 0 = 1 :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_zero hv)).symm

lemma comb_sum' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) {κ : Type}
    (s : Finset κ) (f : κ → Fin n → R) : comb v (∑ j ∈ s, f j) = ∏ j ∈ s, comb v (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using comb_zero' hv
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, comb_add' hv, ih]

lemma comb_comb' {n m : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (w : Fin m → (epsR R ⟶ G)) (B : Fin m → Fin n → R) (hw : ∀ j, w j = comb v (B j)) (g : Fin m → R) :
    comb w g = comb v (∑ j, g j • B j) := by
  rw [comb_sum' hv]
  unfold comb
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hw j]
  exact epsScale_comb v (B j) (g j)

lemma comb_comp_hom' {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f]
    {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) :
    comb v c ≫ f = comb (fun i => v i ≫ f) c :=
  (isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_comp f ((isLieComb_iff_comb _ _ _).2 rfl))

end
end GlobalTheory.PtDeg.FrameExact


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in
theorem GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (f : P.A ⟶ P.A) (M : F.P₀.A ⟶ F.P₀.A) [IsMonHom M] (L : Module.End K (Fin F.P₀.g → K)), F.IsDiffOf F f L → Over.Hom.left M ≫ F.φ = F.φ ≫ Over.Hom.left f → ∀ c : Fin F.P₀.g → K, GlobalTheory.Reg.VecEig.comb F.v c ≫ M = GlobalTheory.Reg.VecEig.comb F.v (L c) := by
  intro K _ _ P F f M _ L hL hM
  have hv := F.basis
  let Sg : Submodule K (Fin F.P₀.g → K) :=
    { carrier := {c | comb F.v c ≫ M = comb F.v (L c)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [comb_add' hv.1, map_add (f := _), comb_add' hv.1, ← ha, ← hb, MonObj.mul_comp]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, comb_zero' hv.1, MonObj.one_comp]
      smul_mem' := by
        intro s a ha
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, ← epsScale_comb, ← epsScale_comb, ← ha, Category.assoc] }
  have hspan : Submodule.span K {c | ∃ u, F.IsCoord u c} = ⊤ := by
    have := (GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).2
    rw [GlobalTheory.CM.GenFib.lieLat, Submodule.span_span_of_tower] at this
    exact this
  have hpb : IsPullback F.φ F.P₀.A.hom P.A.hom (spMap (algebraMap (𝓞 K) K)) := F.fib.2.1.1
  have hsub : {c | ∃ u, F.IsCoord u c} ⊆ (Sg : Set _) := by
    rintro c ⟨u, hut, w, hwv, hwc⟩
    obtain ⟨hut', w', hw'v, hw'c⟩ := hL u c ⟨hut, w, hwv, hwc⟩
    obtain ⟨z, -, hz⟩ := GlobalTheory.existsUnique_isVecOver hpb (u ≫ f)
    have hwM : GlobalTheory.IsVecOver (algebraMap (𝓞 K) K) F.φ (u ≫ f) (w ≫ M) := by
      unfold GlobalTheory.IsVecOver at hwv ⊢
      simp only [Over.comp_left, Category.assoc]
      rw [hM, ← Category.assoc, hwv, Category.assoc]
    have e := (hz _ hwM).trans (hz _ hw'v).symm
    show comb F.v c ≫ M = comb F.v (L c)
    rw [(isLieComb_iff_comb _ _ _).1 hwc] at e
    rw [← (isLieComb_iff_comb _ _ _).1 hw'c, e]
  intro c
  have h := Submodule.span_le.2 hsub
  rw [hspan] at h
  exact h (Submodule.mem_top : c ∈ ⊤)


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in
theorem GlobalTheory.PtDeg.exists_frameCoord_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ' : E →+* ℂ) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ' a)) → ∃ v : Fin (Dw.mult ρ') → Fin F.P₀.g → K, GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ' v ∧ LinearIndependent K v ∧ Submodule.span K (Set.range v) = Submodule.span K (F.eigLat B.t.act t : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ' t ht
  have h1 : IsGrpPullback t₀.G Xo.univ.t.G y.x m1.φ := m1.cart
  have h2 : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have h3 : IsGrpPullback F.P₀.A B.pol.A (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  obtain ⟨⟨ψ, hψ, -⟩, hψm⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h2 h3 (𝟙 _)
  obtain ⟨⟨ψ', hψ', -⟩, hψm'⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h2 (𝟙 _)
  haveI : IsMonHom ψ := hψm ψ hψ inferInstance
  haveI : IsMonHom ψ' := hψm' ψ' hψ' inferInstance
  simp only [Over.id_left, Category.comp_id] at hψ hψ'
  have hψψ' : ψ ≫ ψ' = 𝟙 _ := by
    apply GlobalTheory.Reg.VecEig.pt_ext m2
    simp only [Over.comp_left, Category.assoc, Over.id_left, Category.id_comp]
    rw [hψ', hψ]
  have hψ'ψ : ψ' ≫ ψ = 𝟙 _ := by
    obtain ⟨⟨k, hk, hk1⟩, -⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h3 (𝟙 _)
    have a1 := hk1 (ψ' ≫ ψ) (by simp only [Over.comp_left, Category.assoc, Over.id_left, Category.comp_id]; rw [hψ, hψ'])
    have a2 := hk1 (𝟙 _) (by simp)
    rw [a1, a2]
  obtain ⟨r, hrD, hr⟩ := GlobalTheory.CM.GenFib.exists_lieRep_eigLat K B.pol F (𝓞 E) B.t.act
  have hv := F.basis

  have key : ∀ (u : epsR K ⟶ t₀.G) (d : Fin F.P₀.g → K), u ≫ ψ = comb F.v d → ∀ a : 𝓞 E,
      (u ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ u ↔ r a d = t a • d) := by
    intro u d hud a
    haveI := t₀.act.hom a
    have hM : Over.Hom.left (ψ' ≫ t₀.act.act a ≫ ψ) ≫ F.φ = F.φ ≫ Over.Hom.left (B.t.act.act a) := by
      simp only [Over.comp_left, Category.assoc, hψ]
      have := m2.act a
      simp only [SABMap.φ] at hψ' ⊢
      rw [this, ← Category.assoc, hψ']
    have hE := GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf K B.pol F (B.t.act.act a) (ψ' ≫ t₀.act.act a ≫ ψ) (r a) (hrD a) hM d
    rw [← hud] at hE
    have hE' : u ≫ t₀.act.act a ≫ ψ = comb F.v (r a d) := by
      rw [← hE]; simp only [Category.assoc, reassoc_of% hψψ']
    have hs : comb F.v (((t a : 𝓞 K) : K) • d) = epsScale ((t a : 𝓞 K) : K) ≫ u ≫ ψ := by
      rw [hud, epsScale_comb]
    have hsm : ((t a : 𝓞 K) : K) • d = t a • d := algebraMap_smul K (t a) d
    constructor
    · intro h
      apply comb_injective hv
      rw [← hE', ← hsm, hs, ← Category.assoc, h, Category.assoc]
    · intro h
      have h' : (u ≫ t₀.act.act a) ≫ ψ = (epsScale ((t a : 𝓞 K) : K) ≫ u) ≫ ψ := by
        rw [Category.assoc, hE', h, ← hsm, hs, Category.assoc]
      have := congrArg (· ≫ ψ') h'
      simpa only [Category.assoc, hψψ', reassoc_of% hψψ', Category.comp_id] using this

  have hlift : ∀ i, ∃ u : epsR K ⟶ t₀.G, Over.Hom.left u ≫ m1.φ = y.u ρ' i :=
    fun i => GlobalTheory.KSExist.FrameLift.exists_lift h1 (T := epsR K) (y.u ρ' i) (y.tan ρ' i).1
  choose U hU using hlift
  have hUt : ∀ i, IsTangent (U i) := fun i =>
    (GlobalTheory.KSExist.FrameLift.tan_iff h1 (U i)).1 (by rw [hU]; exact y.tan ρ' i)
  have hUe : ∀ i a, U i ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ U i := fun i a =>
    (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (U i) _).1 (by
      have := y.eig ρ' i a
      rw [hU, ht]; simpa only [Category.assoc] using this)
  have hWt : ∀ i, IsTangent (U i ≫ ψ) := fun i => GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ (hUt i)
  have hco : ∀ i, ∃ d, U i ≫ ψ = comb F.v d := fun i => by
    obtain ⟨d, hd, -⟩ := hv.2 _ (hWt i)
    exact ⟨d, (isLieComb_iff_comb _ _ _).1 hd⟩
  choose V hV using hco
  have hUy : (fun i => Over.Hom.left (U i) ≫ m1.φ) = y.u ρ' := funext hU
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Over.Hom.left (U i), U i ≫ ψ, hU i, ?_, ?_⟩
    · simp only [Over.comp_left, Category.assoc, hψ]
    · rw [isLieComb_iff_comb]; exact hV i
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have e1 : comb U g ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV, hg]
    have e0 : comb U 0 ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV]; simp
    have hW : comb U g = comb U 0 := by
      have := congrArg (· ≫ ψ') (e1.trans e0.symm)
      simpa only [Category.assoc, hψψ', Category.comp_id] using this
    have c1 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U g (comb U g) ((isLieComb_iff_comb _ _ _).2 rfl)
    have c0 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U 0 (comb U g) ((isLieComb_iff_comb _ _ _).2 hW)
    rw [hUy] at c1 c0
    have htan := GlobalTheory.ReframeClauses.isTanAt_of_isCombAt (y.tan ρ') c1
    have heig := GlobalTheory.ReframeClauses.isEigAt_of_isCombAt (y.tan ρ') (y.eig ρ') c1
    obtain ⟨a0, -, huniq⟩ := y.basis ρ' _ htan heig
    have := (huniq g c1).trans (huniq 0 c0).symm
    intro i
    simpa using congrFun this i
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ((hr t (V i)).2).2 fun a => (key (U i) (V i) (hV i) a).1 (hUe i a)
    · intro d hd
      have hd' := ((hr t d).2).1 hd
      have hwt : IsTangent (comb F.v d) := isTangent_comb hv.1 d
      have hu : (comb F.v d ≫ ψ') ≫ ψ = comb F.v d := by
        simp only [Category.assoc, hψ'ψ, Category.comp_id]
      have hut : IsTangent (comb F.v d ≫ ψ') := GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ' hwt
      have hue : ∀ a, (comb F.v d ≫ ψ') ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ (comb F.v d ≫ ψ') :=
        fun a => (key _ d hu a).2 (hd' a)
      have htan : IsTanAt y.x (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) :=
        (GlobalTheory.KSExist.FrameLift.tan_iff h1 _).2 hut
      have heig : IsEigAt c ρ' (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) := fun a => by
        have := (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (comb F.v d ≫ ψ') _).2 (hue a)
        rw [← ht]; simpa only [Category.assoc] using this
      obtain ⟨g, hg, -⟩ := y.basis ρ' _ htan heig
      rw [← hUy] at hg
      have hl := GlobalTheory.KSExist.FrameLift.isLieComb_of_isCombAt h1 U g _ hg
      rw [isLieComb_iff_comb] at hl
      have hdd : comb F.v d = comb F.v (∑ j, g j • V j) := by
        rw [← hu, hl, comb_comp_hom', comb_comb' hv.1 _ V hV]
      rw [comb_injective hv hdd]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (cj j h₀ x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x)) := by
  first | exact @GlobalTheory.DivTransfer.divAt_cj_iff | exact GlobalTheory.DivTransfer.divAt_cj_iff | (intros; apply GlobalTheory.DivTransfer.divAt_cj_iff <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

theorem _root_.GlobalTheory.T.zeta_integral_equivariant_nonzero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.GJForm.isEqv_integral_and_ne_zero | exact GlobalTheory.GJForm.isEqv_integral_and_ne_zero | (intros; apply GlobalTheory.GJForm.isEqv_integral_and_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.unitLattice_stable_iff_conj_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  first | exact @GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | exact GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | (intros; apply GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff <;> assumption)
end
