module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle497
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472

@[expose] public section

section

noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.CompanionTheory.ThTot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProdMeasPf

section Abstract

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isAddFundamentalDomain_join (J : X × Y ≃ᵐ Z) (hJ : ∀ a b, J (a + b) = J a + J b)
    (Γ : AddSubgroup X) (Δ : AddSubgroup Y) (Λ : AddSubgroup Z)
    (hΛ : ∀ z, z ∈ Λ ↔ (J.symm z).1 ∈ Γ ∧ (J.symm z).2 ∈ Δ)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (F : Set X) (G : Set Y)
    (hF : IsAddFundamentalDomain Γ F μ) (hG : IsAddFundamentalDomain Δ G ν) :
    IsAddFundamentalDomain Λ (J '' (F ×ˢ G)) ((μ.prod ν).map J) := by
  have hm : ∀ R : Set (X × Y), (μ.prod ν).map J (J '' R) = μ.prod ν R := fun R => by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective]
  have htr : ∀ (l : Z) (w : X × Y), l + J w = J (J.symm l + w) := fun l w => by
    rw [hJ, J.apply_symm_apply]
  have himg : ∀ l : Λ, (l +ᵥ (J '' (F ×ˢ G)) : Set Z) =
      J '' ((((⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) +ᵥ F : Set X)) ×ˢ
        (((⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) +ᵥ G : Set Y))) := by
    intro l
    ext z
    constructor
    · rintro ⟨_, ⟨w, ⟨h1, h2⟩, rfl⟩, rfl⟩
      refine ⟨J.symm l.1 + w, ⟨⟨w.1, h1, rfl⟩, ⟨w.2, h2, rfl⟩⟩, ?_⟩
      exact (htr l.1 w).symm
    · rintro ⟨w, ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩, rfl⟩
      refine ⟨J (a, b), ⟨(a, b), ⟨ha, hb⟩, rfl⟩, ?_⟩
      have : J.symm l.1 + (a, b) = w := Prod.ext h1 h2
      change l.1 + J (a, b) = J w
      rw [htr, this]
  refine ⟨?_, ?_, ?_⟩
  · have hq : QuasiMeasurePreserving J.symm ((μ.prod ν).map J) (μ.prod ν) := by
      refine ⟨J.symm.measurable.aemeasurable, ?_⟩
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    rw [J.image_eq_preimage_symm]
    exact (hF.nullMeasurableSet.prod hG.nullMeasurableSet).preimage hq
  · rw [J.measurableEmbedding.ae_map_iff]
    have h1 := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hF.ae_covers
    have h2 := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hG.ae_covers
    filter_upwards [h1, h2] with w hw1 hw2
    obtain ⟨g, hg⟩ := hw1
    obtain ⟨d, hd⟩ := hw2
    refine ⟨⟨J (g.1, d.1), (hΛ _).2 (by simp)⟩, (g.1 + w.1, d.1 + w.2), ⟨hg, hd⟩, ?_⟩
    change J (g.1 + w.1, d.1 + w.2) = J (g.1, d.1) + J w
    rw [← hJ]
    rfl
  · intro l l' hll
    change (μ.prod ν).map J ((l +ᵥ (J '' (F ×ˢ G)) : Set Z) ∩ (l' +ᵥ (J '' (F ×ˢ G)) : Set Z)) = 0
    rw [himg, himg, ← Set.image_inter J.injective, hm, Set.prod_inter_prod, Measure.prod_prod]
    have hne : (⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) ≠ ⟨(J.symm l'.1).1, ((hΛ _).1 l'.2).1⟩ ∨
        (⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) ≠ ⟨(J.symm l'.1).2, ((hΛ _).1 l'.2).2⟩ := by
      by_contra hcon
      push_neg at hcon
      apply hll
      apply Subtype.ext
      apply J.symm.injective
      exact Prod.ext (congrArg Subtype.val hcon.1) (congrArg Subtype.val hcon.2)
    rcases hne with h | h
    · have := hF.aedisjoint h
      rw [show μ _ = 0 from this, zero_mul]
    · have := hG.aedisjoint h
      rw [show ν _ = 0 from this, mul_zero]

end Abstract

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j; simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j; simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem rowJ_add (x x' : Mx D r p) (z z' : Mx D s p) : rowJ (x + x') (z + z') = rowJ x z + rowJ x' z' := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowJ]
  | right b => simp [rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simpa [rowJ] using (continuous_fst.matrix_elem a j)
  | right b =>
    simpa [rowJ] using (continuous_snd.matrix_elem b j)

def rowH : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := Prod.ext (rowT_rowJ _ _) (rowB_rowJ _ _)
  right_inv := rowJ_rowT_rowB
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem mem_ratMx_iff (y : Mx D (r + s) p) :
    y ∈ ratMx D (r + s) p ↔ rowT y ∈ ratMx D r p ∧ rowB y ∈ ratMx D s p := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨fun i j => γ (Fin.castAdd s i) j, rfl⟩, ⟨fun i j => γ (Fin.natAdd r i) j, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    replace ha : rat a = rowT y := ha
    replace hb : rat b = rowB y := hb
    refine ⟨fun i j => Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) i, ?_⟩
    change rat _ = y
    funext i j
    induction i using Fin.addCases with
    | left u =>
      refine Eq.trans ?_ (congrFun (congrFun ha u) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.castAdd s u)) =
        incA D (a u j)
      rw [Fin.addCases_left]
    | right v =>
      refine Eq.trans ?_ (congrFun (congrFun hb v) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.natAdd r v)) =
        incA D (b v j)
      rw [Fin.addCases_right]

theorem prodMeas : ProdMeas := by
  intro D r s p μr 𝓕r μs 𝓕s μ 𝓕 hr hs h
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D r p
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D s p
  obtain ⟨c1, c2, c3, c4, -⟩ := lattice_Mx D (r + s) p
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  let J : Mx D r p × Mx D s p ≃ᵐ Mx D (r + s) p := (rowH (D := D) (r := r) (s := s) (p := p)).toMeasurableEquiv
  have hJ : ∀ a b, J (a + b) = J a + J b := fun a b => rowJ_add a.1 b.1 a.2 b.2
  have hJf : (J : Mx D r p × Mx D s p → Mx D (r + s) p) = fun z => rowJ z.1 z.2 := rfl
  let e : Mx D r p × Mx D s p ≃+ Mx D (r + s) p :=
    { (rowH (D := D) (r := r) (s := s) (p := p)).toEquiv with map_add' := hJ }
  have hH : ((μr.prod μs).map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μr.prod μs) e continuous_rowJ (continuous_rowT.prodMk continuous_rowB)
  have hF : IsAddFundamentalDomain (ratMx D (r + s) p) (J '' (𝓕r ×ˢ 𝓕s)) ((μr.prod μs).map J) :=
    isAddFundamentalDomain_join J hJ (ratMx D r p) (ratMx D s p) (ratMx D (r + s) p)
      (fun z => mem_ratMx_iff z) μr μs 𝓕r 𝓕s hr.2.1 hs.2.1
  have h1 : (μr.prod μs).map J (J '' (𝓕r ×ˢ 𝓕s)) = 1 := by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective, Measure.prod_prod, hr.2.2, hs.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (r + s) p) ((μr.prod μs).map J) (J '' (𝓕r ×ˢ 𝓕s)) := ⟨hH, hF, h1⟩
  exact covolOne_measure_eq hcov h

end GlobalTheory.CompanionTheory.ThTot.ProdMeasPf
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {p : ℕ}

theorem mx_zero_subsingleton : Subsingleton (Mx D 0 p) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem one_mem_schwartzA_zero (θ : InfFam D) : (fun _ => 1 : Mx D 0 p → ℂ) ∈ schwartzA θ 0 p := by
  refine Submodule.subset_span ?_
  let f : SchwartzMap (D.what₂.Tau → Fin 0 → Fin p → ℂ) ℂ :=
    { toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        refine ⟨1, fun x => ?_⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst hx
        rcases k with _ | k
        · rcases n with _ | n
          · simp
          · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
        · simp }
  refine ⟨f, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, ?_⟩
  · exact (Set.subsingleton_of_subsingleton).isCompact
  · funext x
    exact (mul_one (1 : ℂ)).symm

theorem pr_zero (b₀ : HermE D 0) (x y : Mx D 0 p) : pr b₀ x y = 0 := by
  ext i j
  simp [pr, HMul.hMul]

theorem isTh_one {μ : Measure (Mx D 0 p)} (h1 : μ Set.univ = 1) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (b₀ : HermE D 0) : IsTh ψ 1 θ b₀ μ (fun _ _ => 1) := by
  have : IsProbabilityMeasure μ := ⟨h1⟩
  refine ⟨fun _ => one_mem_schwartzA_zero θ, continuous_const, ?_, ?_, ?_, ?_⟩
  · intro C _
    exact ⟨_, one_mem_schwartzA_zero θ, fun _ _ _ => le_rfl⟩
  · intro g a _ h y
    simp [npow]
  · intro g b _ h y
    simp [pr_zero, halfTr]
  · intro g _ h x
    simp [pr_zero]

theorem zeroTotal : ZeroTotal := by
  intro D p μ 𝓕 h ψ hψ b₀ θ hθ u hu hB hall
  have hs : Subsingleton (Mx D 0 p) := mx_zero_subsingleton
  obtain ⟨-, -, hF⟩ := h
  have hne : 𝓕.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝓕 with he | hn
    · simp [he] at hF
    · exact hn
  have huniv : 𝓕 = Set.univ := by
    obtain ⟨y, hy⟩ := hne
    exact Set.eq_univ_of_forall fun z => (Subsingleton.elim z y) ▸ hy
  have h1 : μ Set.univ = 1 := huniv ▸ hF
  have : IsProbabilityMeasure μ := ⟨h1⟩
  have h0 := hall _ (isTh_one h1 ψ θ b₀)
  have hc : (fun y => u y * conj (1 : ℂ)) = fun _ => u 0 := by
    funext y
    simp [Subsingleton.elim y 0]
  have h2 : u 0 = 0 := by
    have h3 : ∫ y, u y * conj (1 : ℂ) ∂μ = 0 := h0
    rw [hc] at h3
    simpa using h3
  funext y
  rw [Subsingleton.elim y 0, h2]
  rfl

end GlobalTheory.CompanionTheory.ThTot

end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealMult.DiracProof

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem expU_add' (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

theorem weight_int (h : IsDerivK σ Kf) (a : Fin n) (r : ℝ) {v : V} (hv : v ≠ 0)
    (hr : Kf a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → V := fun s => σ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := deriv_expU (Kf := Kf) h X hX v
    have e := sum_single (Kf := Kf) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : V →L[ℝ] V :=
      ((LinearMap.isometryOfInner (σ (expU X hX s)) (h.1 _)).toContinuousLinearMap).restrictScalars ℝ
    have hL : ∀ y, L y = σ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add']
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, Module.End.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → V := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show σ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one, Module.End.one_apply]
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

theorem kF_gl {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h.comm a b c d, h.comm c d a b]
    abel
  rw [e, h1, h2]
  split_ifs <;> simp [kF] <;> abel

end GlobalTheory.CompanionTheory.RealMult.DiracProof

namespace GlobalTheory.CompanionTheory.RealMult

end GlobalTheory.CompanionTheory.RealMult
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_to_acris_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | exact GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

theorem _root_.GlobalTheory.T.compare_quotient_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ), Function.Bijective ((cmpq A l n).f i) := by
  first | exact @GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | exact GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | (intros; apply GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective <;> assumption)
end
