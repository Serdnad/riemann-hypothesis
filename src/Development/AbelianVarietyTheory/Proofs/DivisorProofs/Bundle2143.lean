module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.isCompact_level_height_scales_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  first | exact @GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | exact GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | (intros; apply GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_conj_eq_of_semidirectLatticeDatum : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ m ∈ M, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (m * u * m⁻¹) ∂ν = ∫⁻ u : N, f u ∂ν := by
  first | exact @GlobalTheory.ResLine.lintegral_conj_eq_of_semiLat | exact GlobalTheory.ResLine.lintegral_conj_eq_of_semiLat | (intros; apply GlobalTheory.ResLine.lintegral_conj_eq_of_semiLat <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.height_function_compact_level_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  first | exact @GlobalTheory.ResLine.HtCont.isCompact_and_continuous | exact GlobalTheory.ResLine.HtCont.isCompact_and_continuous | (intros; apply GlobalTheory.ResLine.HtCont.isCompact_and_continuous <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine.LowerAverage

theorem countable_subgroupOf {G : Type} [Group G] (Λ N : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf N) := by
  refine Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : Λ)) ?_
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Λ => (z : G)) h))

theorem right_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (N Λ : Subgroup G) [Countable Λ] (hN : IsClosed (N : Set G)) (ν : Measure N)
    (hν : ν.IsHaarMeasure) (D : Set N) (hD : IsFundamentalDomain (Λ.subgroupOf N) D ν)
    (hfin : ν D ≠ ⊤) : ν.IsMulRightInvariant := by
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set G))
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_subgroupOf Λ N
  exact RightUnfold.isMulRightInvariant_of_lattice ν (Λ.subgroupOf N) D hD hfin

theorem average_lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ C : Set G, IsCompact C → ∃ (U : Set G) (c : ℝ≥0∞), IsOpen U ∧ μ U ≠ ⊤ ∧ c ≠ 0 ∧ ∀ u₀ ∈ N, ∀ m₀ ∈ M, ∀ y ∈ C, c ≤ ∫⁻ m : M, ∫⁻ u : N, U.indicator 1 ((u : G) * m * (u₀ * m₀ * y)) ∂ν ∂π := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM H μ hμ C hC
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set G))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set G))
  haveI := H.haarN
  haveI := H.haarM
  haveI := right_of_closed N Λ H.closedN ν H.haarN DN H.domN H.finN
  haveI := right_of_closed M Λ H.closedM π H.haarM DM H.domM H.finM
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  obtain ⟨W, hW, hWC⟩ := compact_open_separated_mul_left hC isOpen_interior hCK
  obtain ⟨V, hVo, hV1, hVW⟩ := exists_open_nhds_one_mul_subset hW
  have hVN : IsOpen ((↑) ⁻¹' V : Set N) := hVo.preimage continuous_subtype_val
  have hVM : IsOpen ((↑) ⁻¹' V : Set M) := hVo.preimage continuous_subtype_val
  refine ⟨interior K, ν ((↑) ⁻¹' V) * π ((↑) ⁻¹' V), isOpen_interior,
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne,
    mul_ne_zero (hVN.measure_ne_zero ν ⟨1, hV1⟩) (hVM.measure_ne_zero π ⟨1, hV1⟩), ?_⟩
  intro u₀ hu₀ m₀ hm₀ y hy
  have h1 : ∀ m : M, ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞) ((u : G) * m * (u₀ * m₀ * y)) ∂ν
      = ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y) ∂ν := by
    intro m
    rw [← lintegral_mul_right_eq_self (fun u : N => (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y)) ⟨m * u₀ * (m : G)⁻¹, H.norm m m.2 u₀ hu₀⟩]
    refine lintegral_congr fun u => ?_
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [h1]
  rw [lintegral_mul_right_eq_self (fun m : M => ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * (m : G) * y) ∂ν) ⟨m₀, hm₀⟩, ← lintegral_indicator_const hVM.measurableSet]
  refine lintegral_mono fun m => ?_
  by_cases hm : m ∈ ((↑) ⁻¹' V : Set M)
  swap
  · rw [Set.indicator_of_notMem hm]
    exact bot_le
  rw [Set.indicator_of_mem hm]
  rw [← lintegral_indicator_one hVN.measurableSet]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ((↑) ⁻¹' V : Set N)
  swap
  · rw [Set.indicator_of_notMem hu]
    exact bot_le
  rw [Set.indicator_of_mem hu]
  have : (u : G) * m * y ∈ interior K :=
    hWC (Set.mul_mem_mul (hVW (Set.mul_mem_mul hu hm)) hy)
  rw [Set.indicator_of_mem this]
  exact le_rfl

end GlobalTheory.ResLine.LowerAverage
end

section

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

section Comb

open DeRham Cris MonObj

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : epsR R ⟶ A :=
  (List.ofFn fun i => GrpTangent.epsScale (cf i) ≫ v i).prod

theorem isLieComb_lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : IsLieComb cf v (lieComb cf v) :=
  ⟨_, fun _ => rfl, rfl⟩

theorem rel_lieComb {N : Type*} [AddCommMonoid N] [Module R N] {P : N → (epsR R ⟶ A) → Prop} (h0 : P 0 1)
    (ha : ∀ {f f' v v'}, P f v → P f' v' → P (f + f') (v * v'))
    (hs : ∀ {f v}, P f v → ∀ r : R, P (r • f) (GrpTangent.epsScale r ≫ v)) :
    ∀ {n : ℕ} (cf : Fin n → R) {f : Fin n → N} {v : Fin n → (epsR R ⟶ A)}, (∀ i, P (f i) (v i)) →
      P (∑ i, cf i • f i) (lieComb cf v)
  | 0, _, _, _, _ => by simpa [lieComb] using h0
  | n + 1, cf, f, v, h => by
    rw [Fin.sum_univ_succ, lieComb, List.ofFn_succ, List.prod_cons]
    exact ha (hs (h 0) _) (rel_lieComb h0 ha hs (fun i => cf i.succ) fun i => h i.succ)

theorem isLieImage_lieComb {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (h : ∀ i, DeRham.IsLieImage (f i) (v i)) : DeRham.IsLieImage (∑ i, cf i • f i) (lieComb cf v) :=
  rel_lieComb (isLieImage_one_iff.2 (zero_mem _)) IsLieImage.add IsLieImage.smul cf h

theorem isKSValue_lieComb {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    {h : IsGrpPullback A A' (_root_.GlobalTheory.DeRham.epsRed R) i} {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (e : ∀ k, IsKSValue h (f k) (v k)) : IsKSValue h (∑ k, cf k • f k) (lieComb cf v) :=
  rel_lieComb ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
    IsKSValue.add IsKSValue.smul cf e

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

theorem isLieComb_iff_isCombAt {A : Over (Sp K)} [GrpObj A] {x : Sp K ⟶ Xo.X} {π : A.left ⟶ Xo.univ.t.G.left}
    (h : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (cf : Fin n → K) (v : Fin n → (epsR K ⟶ A)) (w : epsR K ⟶ A) :
    IsLieComb cf v w ↔ IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) :=
  Chart.comb_push h cf v w

def ksChg (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (HIx Dw Φ → K) →ₗ[K] (HIx Dw Φ → K) where
  toFun M k := ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2
  map_add' M M' := by ext k; simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by ext k; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem ksChg_apply (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (k : HIx Dw Φ) :
    ksChg Φ g M k = ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2 := rfl

theorem ksChg_eq_mul (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (τ : Φ) : (Matrix.of fun a b => ksChg Φ g M ⟨τ, a, b⟩) =
      (g (conjEmb τ.1)).transpose * (Matrix.of fun a b => M ⟨τ, a, b⟩) * g τ.1 := by
  ext a b
  simp only [Matrix.of_apply, ksChg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ksChg_ksChg (Φ : Finset (E →+* ℂ)) (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) : ksChg Φ g (ksChg Φ g' M) = ksChg Φ (fun τ => g' τ * g τ) M := by
  funext ⟨τ, a, b⟩
  have h : (Matrix.of fun a b => ksChg Φ g (ksChg Φ g' M) ⟨τ, a, b⟩) =
      Matrix.of fun a b => ksChg Φ (fun τ => g' τ * g τ) M ⟨τ, a, b⟩ := by
    simp only [ksChg_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  exact congrFun (congrFun h a) b

theorem ksChg_one (Φ : Finset (E →+* ℂ)) (M : HIx Dw Φ → K) : ksChg Φ (fun _ => 1) M = M := by
  funext ⟨τ, a, b⟩
  have h := ksChg_eq_mul Φ (fun _ => 1) M τ
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact congrFun (congrFun h a) b

theorem exists_frChg_inv {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') :
    ∃ g' a', FrChg g' a' y' y ∧ (∀ τ, g' τ * g τ = 1) ∧ ∀ τ, g τ * g' τ = 1 := by
  obtain ⟨g', a', -, h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have e := ((frChg_exists_unique E H Dw l Xo c K y y).2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h).1 h') (C.2.1 y)).1
  have e' := ((frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')).1
  exact ⟨g', a', h', congrFun e, congrFun e'⟩

theorem smul_sum_smul_sum {N α β γ : Type} [AddCommGroup N] [Module K N] [Fintype α] [Fintype β] [Fintype γ]
    (p : α → K) (M : α → β → K) (q : β → γ → K) (n : γ → N) :
    ∑ a, p a • ∑ b, M a b • ∑ k, q b k • n k = ∑ k, (∑ a, ∑ b, p a * M a b * q b k) • n k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm


open DeRham Cris in
theorem IsKS.of_frChg {Φ : Finset (E →+* ℂ)} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    {a : K} {y y' : FrPt Xo c K} (h : FrChg g a y y') {x' : Sp (DualNumber K) ⟶ Xo.X} {M' : HIx Dw Φ → K}
    (hM : IsKS Φ y' x' M') : IsKS Φ y x' (ksChg Φ g M') := by
  obtain ⟨g', a', h', e, -⟩ := exists_frChg_inv h
  obtain ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hψ, hub, hhb, hrow⟩ := hM
  rw [h.1] at hπ
  obtain ⟨N, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
  choose n hn using fun σ k => (htan _).1 (y.tan σ k)
  have hn' : ∀ σ k, y'.u σ k = v (∑ j, g σ k j • n σ j) := fun σ k => by
    have := h.2.1 σ k
    rwa [show y.u σ = fun j => v (n σ j) from funext fun j => (hn σ j).symm, hcomb] at this
  have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → N) (w : epsR K ⟶ A),
      (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
    fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
  have hub' : ∀ σ k, (ub σ k).left ≫ π = v (∑ j, g σ k j • n σ j) := fun σ k => (hub σ k).trans (hn' σ k)
  have hu : ∀ σ k, (lieComb (g' σ k) (ub σ)).left ≫ π = v (n σ k) := fun σ k => by
    rw [(key _ _ _ _ (hub' σ)).1 (isLieComb_lieComb _ _)]
    congr 1
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, e, Matrix.one_apply]
    simp
  refine ⟨A, _, A', _, π, π', i, hi, ψ, fun σ k => lieComb (g' σ k) (ub σ),
    fun q => ∑ j, g' q.1 q.2 j • hb ⟨q.1, j⟩, hπ, hπ', hiπ, hψ, fun σ k => (hu σ k).trans (hn σ k),
    fun σ k => isLieImage_lieComb _ (hhb σ), fun τ a => ?_⟩
  choose w hw f hf hd hv using hrow τ
  refine ⟨lieComb (fun a' => g (conjEmb τ.1) a' a) w, (key _ _ _ _ (hu τ.1)).2 ?_,
    ∑ a', g (conjEmb τ.1) a' a • f a', Submodule.sum_mem _ fun a' _ => Submodule.smul_mem _ _ (hf a'),
    fun ⟨σ, k⟩ => ?_, isKSValue_lieComb _ hv⟩
  · rw [(key _ _ _ _ fun a' => (key _ _ _ _ (hub' τ.1)).1 (hw a')).1 (isLieComb_lieComb _ _)]
    congr 1
    exact smul_sum_smul_sum _ (fun a' b' => M' ⟨τ, a', b'⟩) _ _

  · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul]
    by_cases hσ : σ = conjEmb τ.1
    · subst hσ
      have := congrFun (congrFun (e (conjEmb τ.1)) k) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    · simp [hσ]

theorem isKS_frChg_iff (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (a : K) (y y' : FrPt Xo c K) (h : FrChg g a y y') (x' : Sp (DualNumber K) ⟶ Xo.X) (M' : HIx Dw Φ → K) :
    IsKS Φ y' x' M' ↔ IsKS Φ y x'
      (fun k => ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M' ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2) := by
  refine ⟨fun k => k.of_frChg h, fun k => ?_⟩
  obtain ⟨g', a', h', -, e⟩ := exists_frChg_inv h
  have := IsKS.of_frChg h' (M' := ksChg Φ g M') k
  rwa [ksChg_ksChg, funext e, ksChg_one] at this

end GlobalTheory.FlagTan
end
end

section

set_option autoImplicit false


noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open scoped Classical

namespace GlobalTheory.FlagTan

open GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]


variable (Dw K) in
def horExt (Φ : Finset (E →+* ℂ)) : (HIx Dw Φ → K) →ₗ[K] (TIx Dw Φ → K) :=
  LinearMap.pi fun b => Sum.elim (fun k => LinearMap.proj k) (fun _ => 0) b


variable (c) in
def horMap (Φ : Finset (E →+* ℂ)) : TrivSqZeroExt K (HIx Dw Φ → K) →ₐ[c.F] TrivSqZeroExt K (TIx Dw Φ → K) :=
  (TrivSqZeroExt.map (horExt Dw K Φ)).restrictScalars c.F

theorem fst_horMap {Φ : Finset (E →+* ℂ)} (a : TrivSqZeroExt K (HIx Dw Φ → K)) : (horMap c Φ a).fst = a.fst :=
  fst_map _ a

theorem dir_horMap {Φ : Finset (E →+* ℂ)} (m : TIx Dw Φ → K) (a : TrivSqZeroExt K (HIx Dw Φ → K)) :
    dir c m (horMap c Φ a) = dir c (m ∘ Sum.inl) a := by
  ext
  · simp [fst_horMap]
  · simp [snd_dir, horMap, horExt, Fintype.sum_sum_type]

def vertDirs (Φ : Finset (E →+* ℂ)) : FIx Dw → TIx Dw Φ → K :=
  fun k b => Sum.elim (fun _ => 0) (fun w : VIx Dw => if k = w.toF then 1 else 0) b

end GlobalTheory.FlagTan



open GlobalTheory.FlagTan GlobalTheory.Frames GlobalTheory.AllWt in
open TrivSqZeroExt hiding map lift in
theorem GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  intro E _ _ _ H Dw l Xo c Y X K _ _ P hK
  obtain ⟨XH, h1, h2, hU⟩ := hK
  obtain ⟨WH, rfl, hWH⟩ := exists_lift P XH h1 h2
  obtain ⟨W₀, hW₀⟩ := exists_frMap (horMap c (K := K) (Dw := Dw) (psiSet H)) WH
  let n : FIx Dw → TIx Dw (psiSet H) → K := vertDirs (psiSet H)
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : TIx Dw (psiSet H) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => ∑ b, n k b * m b) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip]
    · ext <;> simp [unip₀]
  have shift : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u →
      ∃ z₀, FrMap (dir c m) W₀ z₀ ∧ IsShift (fun k => ∑ b, n k b * m b) z₀ u := fun m u hu => by
    obtain ⟨z₀, hz₀⟩ := exists_frMap (dir c m) W₀
    obtain ⟨z, hz, -⟩ := existsUnique_isShift (fun k => ∑ b, n k b * m b) z₀
    exact ⟨z₀, hz₀, frMap_unique (key m z₀ z hz₀ hz) hu ▸ hz⟩
  have hbase : ∀ (m : TIx Dw (psiSet H) → K) (z₀ : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      FrMap (dir c (m ∘ Sum.inl)) WH z₀ := fun m z₀ h => frMap_comp hW₀ h fun a => dir_horMap m a
  have hfst : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W P := by
    have h0 : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W₀ P :=
      frMap_of_comp hW₀ hWH fun a => fst_horMap (c := c) a
    refine (frMap_iff_frChg hW h0).2 ?_
    convert (frChg_calculus E H Dw l Xo c _).2.1 P using 2 with τ
    · ext i j; by_cases h : i = j <;> simp [unip, Matrix.one_apply, h]
    · simp [unip₀]
  have hdef : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u → IsDef P u :=
    fun m u h => frMap_of_comp h hfst fun a => fst_dir (c := c) m a
  choose v hv using fun b : TIx Dw (psiSet H) => exists_frMap (dir c (Pi.single b (1 : K))) W
  refine ⟨W, v, hfst, hv, ⟨fun k => ?_, fun w => ?_⟩, fun m u P₀ hu hP₀ hpt => ?_⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inl k))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) b) = 0 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have ev : v (.inl k) = z₀ := (existsUnique_isShift 0 z₀).unique hs (isShift_zero z₀)
    have e1 : (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) ∘ Sum.inl = Pi.single k 1 := by
      funext h; simp [Pi.single_apply]
    have hb := hbase _ _ hz₀
    rw [e1] at hb
    have hd := hdef _ _ (hv (.inl k))
    refine ⟨hd, ((hU _ hd.isTanX).2 _).2 ?_⟩
    rw [ev]; exact hb.1
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inr w))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inr w) (1 : K) : TIx Dw (psiSet H) → K) b) =
        Pi.single w.toF 1 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have hc : FrMap (GlobalTheory.FlagTan.cst c K) P z₀ := by
      have hb := hbase _ _ hz₀
      refine frMap_of_comp (ψ := GlobalTheory.FlagTan.cst c K) hWH hb fun a => ?_
      ext <;> simp [snd_dir, Pi.single_apply]
    exact ⟨z₀, hc, hs⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift m u hu
    have hH := hbase m z₀ hz₀
    obtain ⟨t, hB⟩ : ∃ t, FrBor t P₀ u := by
      obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P₀)
      obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P₀) (X.lies_ptY P₀).1 k hz
      obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY P₀)
      obtain ⟨t', ht'⟩ := hQ.exists_frBor (hpt ▸ X.lies_ptY u)
      obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (DualNumber K)
      exact ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    have hd := hdef m u hu
    have e0 : m ∘ Sum.inl = 0 := by
      refine (hU u.x hd.isTanX).1.unique (hs.1.trans hH.1) ?_
      have ed : dir c (0 : HIx Dw (psiSet H) → K) = (cst c K).comp (fstHom c.F K (HIx Dw (psiSet H) → K)) :=
        AlgHom.ext fun a => by ext <;> simp [snd_dir]
      rw [hB.1, hP₀.1, ed, GlobalTheory.FlagMod.spMap_algComp, h2]
    have e0' : ∀ h, m (Sum.inl h) = 0 := fun h => congrFun e0 h
    have hz : z₀ = P₀ := by
      refine frMap_unique (frMap_of_comp hWH hH fun a => ?_) hP₀
      ext <;> simp [snd_dir, e0']
    rw [hz] at hs
    obtain ⟨g, hup, -, hc⟩ := (frBor_iff_frChg _ _ _).1 hB
    obtain ⟨hg, -⟩ := (frChg_exists_unique E H Dw l Xo c _ P₀ u).2 _ _ _ _ hc hs
    have hsum : ∀ w₀ : VIx Dw, ∑ b, n w₀.toF b * m b = m (Sum.inr w₀) := fun w₀ => by
      simp [n, vertDirs, Fintype.sum_sum_type, VIx.toF_injective.eq_iff]
    have ev : ∀ w₀ : VIx Dw, m (Sum.inr w₀) = 0 := by
      rintro ⟨σ, ⟨i, j⟩, hij⟩
      have := congrArg (fun g => (g σ i j).snd) hg
      rw [← hsum]
      simp only [VIx.toF]
      simpa [hup σ i j hij, unip] using this.symm
    funext b
    rcases b with b | b
    · exact e0' b
    · exact ev b
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum


theorem _root_.GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  first | exact @GlobalTheory.LevelRed.exists_levelRed | exact GlobalTheory.LevelRed.exists_levelRed | (intros; apply GlobalTheory.LevelRed.exists_levelRed <;> assumption)
end

section

open GlobalTheory.HTLat

theorem _root_.GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ), (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) → ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  first | exact @GlobalTheory.exists_tate_lev_eq_of_card_torsion | exact GlobalTheory.exists_tate_lev_eq_of_card_torsion | (intros; apply GlobalTheory.exists_tate_lev_eq_of_card_torsion <;> assumption)
end
