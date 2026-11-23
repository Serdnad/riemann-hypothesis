module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
public import Mathlib.Analysis.CStarAlgebra.Classes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinLocSchA

open GlobalTheory.WeilM

theorem exists_open_addStab {X : Type} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ K : AddSubgroup X, IsOpen (K : Set X) ∧ ∀ z, ∀ k ∈ K, g (z + k) = g z := by
  let K : AddSubgroup X :=
    { carrier := {k | ∀ z, g (z + k) = g z}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro a b ha hb z
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha z
        have := ha (z + -a)
        simpa using this.symm }
  refine ⟨K, ?_, fun z k hk => hk z⟩
  have h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z := by
    apply IsCompact.eventually_forall_of_forall_eventually hg.2
    intro z _
    have a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1)) :=
      hg.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun p : X × X => g p.2) :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2
    simp only [hp1, hp2, add_zero]
  have h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z := by
    have : Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this.eventually h1
  apply AddSubgroup.isOpen_of_mem_nhds K (g := 0)
  filter_upwards [h1, h2] with k hk1 hk2
  intro z
  by_cases hz : z ∈ tsupport g
  · exact hk1 z hz
  · by_cases hz' : z + k ∈ tsupport g
    · simpa using (hk2 _ hz').symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem compact_support_locally_constant_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨K, hKo, hK⟩ := exists_open_addStab hg
    refine ⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩
    · intro x hx
      by_contra hc
      apply hx
      simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hc, mul_zero]
    · intro x x' h1 h2
      simp only [pureA, ← h1]
      congr 1
      have e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2) := by
        ext i; simp
      rw [e2]
      exact hK _ _ h2
  | zero =>
    refine ⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro x x' _ _; rfl
  | add Φ Ψ _ _ ihΦ ihΨ =>
    obtain ⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩ := ihΦ
    obtain ⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩ := ihΨ
    refine ⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩
    · intro x hx
      by_cases h : Φ x = 0
      · right; apply hs₂ x; intro h'; apply hx; simp [h, h']
      · left; exact hs₁ x h
    · intro x x' h1 h2
      simp only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]
  | smul a Φ _ ih =>
    obtain ⟨C, K, hC, hK, h0, hs, hi⟩ := ih
    refine ⟨C, K, hC, hK, h0, ?_, ?_⟩
    · intro x hx
      apply hs x
      intro h; apply hx; simp [h]
    · intro x x' h1 h2
      simp only [Pi.smul_apply, hi x x' h1 h2]

end GlobalTheory.FinLocSchA
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.SchwartzTranslate

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def transl (a : κ → AdeleRing (𝓞 F) F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun φ x := φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem SB_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] (b : X) {g : X → ℂ}
    (hg : g ∈ SB X) : (fun y => g (y + b)) ∈ SB X :=
  ⟨hg.1.comp_continuous (continuous_add_const b), hg.2.comp_homeomorph (Homeomorph.addRight b)⟩

theorem pureA_translate (a : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    transl F a (pureA F f g) = pureA F (f.compSubConstCLM ℂ (-fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1))
      (fun y => g (y + fun i => (a i).2)) := by
  funext x
  simp only [transl, LinearMap.coe_mk, AddHom.coe_mk, pureA, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  congr 2
  funext i
  exact map_add _ _ _

theorem schA_translate (a : κ → AdeleRing (𝓞 F) F) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x => φ (x + a)) ∈ schA F κ := by
  have key : schA F κ ≤ (schA F κ).comap (transl F a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show transl F a (pureA F f g) ∈ schA F κ
    rw [pureA_translate]
    exact Submodule.subset_span ⟨_, _, SB_translate _ hg, rfl⟩
  exact key hφ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ,
    (fun x => φ (x + a)) ∈ schA F κ :=
  fun F _ _ _ _ a φ hφ => schA_translate F a hφ

end GlobalTheory.SchwartzTranslate

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SchAConj

open GlobalTheory.WeilM
open scoped Classical

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
    have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => star (f x)) x‖ ≤ C
    rw [e, h]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = star (f x) := rfl

theorem star_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    refine Submodule.subset_span ⟨conjSchwartz f, fun y => star (g y), ⟨hg.1.comp star, ?_⟩, ?_⟩
    · exact hg.2.comp_left (g := star) (star_zero ℂ)
    · funext x
      simp [pureA, conjSchwartz_apply, star_mul']
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ Ψ' _ _ h h' =>
    have := (schA F κ).add_mem h h'
    convert this using 1
    funext x; simp [star_add]
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (star c) h
    convert this using 1
    funext x; simp [star_mul']

end GlobalTheory.SchAConj
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  intro k _ _ _ _ a d _ ν β _ hν ϖ hϖ hνϖ Φ hΦ
  have key : ∀ r ≤ a, Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ)) ⊔
      GlobalTheory.RankCoinv.twistSpan ν β := by
    intro r hr
    induction r with
    | zero => exact Submodule.mem_sup_left ⟨hΦ, fun Y hY => absurd hY (Nat.not_lt_zero _)⟩
    | succ r ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (ih (by omega))
      have := GlobalTheory.T.low_rank_filtration_step k (Fin a) (Fin d) ϖ hϖ ν β hν hνϖ r (by simpa using hr) x hx
      exact Submodule.add_mem _ this (Submodule.mem_sup_right hy)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (key a le_rfl)
  refine ⟨x, hx.1, fun Y hY => hx.2 Y (lt_of_le_of_ne (by simpa using Y.rank_le_card_height) hY), ?_⟩
  have e : Φ - x = y := by rw [← hxy]; abel
  rw [e]; exact hy
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped NNReal ENNReal

namespace GlobalTheory.SplitFlip

theorem lintegral_mul_invT_sq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  intro k _ _ _ _ a d Φ h ν hν
  letI mk : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  letI mM : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI := hν
  set M : Matrix (Fin d) (Fin d) k := (invT h).1 with hM
  set M' : Matrix (Fin d) (Fin d) k := ((invT h)⁻¹).1
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let L : Matrix (Fin a) (Fin d) k ≃ᵐ Matrix (Fin a) (Fin d) k :=
    { toFun := fun Y => Y * M
      invFun := fun Y => Y * M'
      left_inv := fun Y => by simp [Matrix.mul_assoc, hMM']
      right_inv := fun Y => by simp [Matrix.mul_assoc, hM'M]
      measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
      measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable }
  let f0 : Matrix (Fin a) (Fin d) k → (Fin a × Fin d → k) := fun Y p => Y p.1 p.2
  have hEc : Continuous f0 := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  let g0 : (Fin a × Fin d → k) → Matrix (Fin a) (Fin d) k := fun f => Matrix.of fun i j => f (i, j)
  have hEsc : Continuous g0 :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  let E : Matrix (Fin a) (Fin d) k ≃+ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }
  let EM : Matrix (Fin a) (Fin d) k ≃ᵐ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      measurable_toFun := hEc.measurable, measurable_invFun := hEsc.measurable }
  haveI hμ : (ν.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map ν hEc hEsc
  let K : Matrix (Fin a × Fin d) (Fin a × Fin d) k := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin a) (Fin a) k) Mᵀ
  have hK : ∀ Y, K *ᵥ f0 Y = f0 (Y * M) := by
    intro Y; funext p
    simp [K, f0, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply, mul_comm]
  have hdetK : K.det = (((gdet h)⁻¹ ^ a : kˣ) : k) := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose, Fintype.card_fin, ← gdet_invT]
    simp [M, gdet]
  have hu : K.det ≠ 0 := by rw [hdetK]; exact Units.ne_zero _
  have hlam : (Measure.addHaar : Measure k).map (fun x => algebraMap k k K.det * x) =
      (distribHaarChar k (gdet h) ^ a) • (Measure.addHaar : Measure k) := by
    have h2 := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map (Measure.addHaar : Measure k) ((gdet h)⁻¹ ^ a)
    rw [Algebra.algebraMap_self, RingHom.id_apply, hdetK]
    have hcd : distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a) = 1 := by
      rw [map_pow, map_inv, ← mul_pow, mul_inv_cancel₀ distribHaarChar_pos.ne', one_pow]
    calc (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x)
        = (distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a)) •
            (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x) := by rw [hcd, one_smul]
      _ = _ := by rw [mul_smul, h2]
  have h1 := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul k k (Fin a × Fin d) K hu Measure.addHaar inferInstance _ hlam
    (ν.map E) hμ
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have key : ν.map L = (distribHaarChar k (gdet h) ^ a) • ν := by
    apply EM.map_measurableEquiv_injective
    rw [Measure.map_map EM.measurable L.measurable, Measure.map_smul]
    have e1 : (EM ∘ L) = (fun x => K *ᵥ x) ∘ EM := by funext Y; exact (hK Y).symm
    rw [e1, ← Measure.map_map (GlobalTheory.CompanionTheory.SW.DetScale.measurable_mulVec K) EM.measurable]
    exact h1
    exact EM.measurable.aemeasurable
  have hl := lintegral_map_equiv (fun Y => ‖Φ Y‖ₑ ^ 2) L (μ := ν)
  rw [key] at hl
  refine hl.symm.trans ?_
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  simp only [apow, GlobalTheory.SplitWeil.nabs, Complex.cpow_natCast, enorm_pow]
  rw [ENNReal.coe_pow]; congr 1; rw [← ofReal_norm_eq_enorm]; simp

end GlobalTheory.SplitFlip
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem comp_linearAut_smooth_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  intro E _ _ w a b L φ hdet hlc hcs
  haveI hMT : IsModuleTopology (w.adicCompletion E) (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (IsModuleTopology (w.adicCompletion E) (Fin a → Fin b → w.adicCompletion E))
  haveI hLC : LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → w.adicCompletion E))
  let e := LinearMap.equivOfDetNeZero L hdet
  have he : ∀ x, e x = L x := fun x => rfl
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Matrix (Fin a) (Fin b) (w.adicCompletion E) ≃ₜ Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  obtain ⟨U, hUo, hU⟩ := hlc
  refine ⟨⟨U.comap L.toAddMonoidHom, ?_, ?_⟩, ?_, hLC⟩
  · exact hUo.preimage (IsModuleTopology.continuous_of_linearMap L)
  · intro x y hy
    rw [map_add (f := _)]
    exact hU (L x) (L y) hy
  · exact hcs.comp_homeomorph h

end GlobalTheory.LeviDesc
end
