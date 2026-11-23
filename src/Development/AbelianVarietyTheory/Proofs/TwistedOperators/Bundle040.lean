module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]

private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)

private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul _ (measurable_mulVec' A).aemeasurable, IA (Units.mk0 _ hA) rfl,
      hinv, map_mul, mul_smul]

private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl

theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.SwapBlocks

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem smInd_equiv_of_eq [TopologicalSpace G] [IsTopologicalGroup G] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H V) (σ' : Representation ℂ H' V)
    (hσ : ∀ g (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((smInd H σ).Equiv (smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g.1 g.2 g.2
  exact ⟨Representation.Equiv.refl _⟩

end General

section Blocks

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

end Blocks

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

end Local

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_smInd_of_eq [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type} [AddCommGroup W] [Module ℂ W] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd H σ).Equiv (_root_.GlobalTheory.PRep.smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun p => hσ p p.2 p.2
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem parabLower_eq_parab_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]
  simp

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviProj_sumComm_eq_swap_leviProjLower (e : a ⊕ b ≃ n)
    (p : _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e))
    (hp : (p : GL n R) ∈
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))) :
    _root_.GlobalTheory.SmGL.leviProj R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) ⟨p, hp⟩ =
      _root_.GlobalTheory.SmGL.leviTwo R b a
        ((_root_.GlobalTheory.SmGL.leviTwo R a b).symm
          (_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p)).swap := by
  funext x
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  cases x
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) :
      Matrix b b R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) :
      Matrix a a R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl

open ValuativeRel MeasureTheory in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
private theorem deltaHalf_inv_leviTwo_eq_deltaHalf_swap (g : GL a k × GL b k) :
    (_root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two a b))⁻¹ (_root_.GlobalTheory.SmGL.leviTwo k a b g) =
      _root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two b a) (_root_.GlobalTheory.SmGL.leviTwo k b a g.swap) := by
  rw [MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two,
    _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg,
    _root_.GlobalTheory.SmGL.absPow_neg]
  simp only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]
  exact mul_comm _ _

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem jacquet_apply_eq_of_eq {M M' : Type} [Group M] [Group M']
    (π : Representation ℂ G V) (N : Subgroup G) (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N : Set G)) {x : M} {x' : M'} (h : s x = s' x') :
    _root_.GlobalTheory.PRep.jacquet π N s hs x = _root_.GlobalTheory.PRep.jacquet π N s' hs' x' := by
  unfold _root_.GlobalTheory.PRep.jacquet
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [h]

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_twist_jacquet_comp {M M' K : Type} [Group M] [Group M'] [Group K]
    (π : Representation ℂ G V) {N N' : Subgroup G} (hN : N = N') (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N' : Set G)) (φ : K →* M) (φ' : K →* M')
    (hφ : ∀ x, s (φ x) = s' (φ' x)) (χ : M →* ℂˣ) (χ' : M' →* ℂˣ)
    (hχ : ∀ x, χ (φ x) = χ' (φ' x)) :
    Nonempty (Representation.Equiv
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ)
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ').comp φ')) := by
  subst hN
  have h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ =
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ' := by
    refine MonoidHom.ext fun x => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ,
      jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem unipRadLower_eq_unipRad_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.unipRadLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad,
    parabLower_eq_parab_sumComm]
  refine and_congr_right fun _ => ?_
  simp only [Bool.forall_bool]
  exact and_comm

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_apply_eq_fromBlocks (e : a ⊕ b ≃ n) (g : GL a R × GL b R) (u v : a ⊕ b) :
    (_root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) :
        Matrix n n R) (e u) (e v) =
      Matrix.fromBlocks (g.1 : Matrix a a R) 0 0 (g.2 : Matrix b b R) u v := by
  rcases u with u | u <;> rcases v with v | v
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_eq_leviEmb_sumComm_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) =
      _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))
        (_root_.GlobalTheory.SmGL.leviTwo R b a g.swap) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨u, rfl⟩ := e.surjective i
  obtain ⟨v, rfl⟩ := e.surjective j
  have hu : e u = ((Equiv.sumComm b a).trans e) u.swap := by simp
  have hv : e v = ((Equiv.sumComm b a).trans e) v.swap := by simp
  rw [leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]
  rcases u with u | u <;> rcases v with v | v <;> rfl


open ValuativeRel MeasureTheory in
theorem _root_.GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V], (∀ ρ : Representation ℂ (GL a k × GL b k) V, Nonempty ((_root_.GlobalTheory.SmGL.ind₂Lower e ρ).Equiv (_root_.GlobalTheory.SmGL.ind₂ ((Equiv.sumComm b a).trans e) (ρ.comp (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)))) ∧ ∀ π : Representation ℂ (GL n k) V, Nonempty ((_root_.GlobalTheory.SmGL.jac₂Lower e π).Equiv ((_root_.GlobalTheory.SmGL.jac₂ ((Equiv.sumComm b a).trans e) π).comp (MulEquiv.prodComm : GL a k × GL b k ≃* GL b k × GL a k).toMonoidHom)) := by
  intro k _ _ _ _ a b n _ _ _ _ _ _ e V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · unfold _root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂
      _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd
    refine nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _
      fun g hg hg' => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply,
      MulEquiv.coe_toMonoidHom]
    rw [leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]
    simp
  · unfold _root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower
      _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU
    rw [MonoidHom.comp_assoc]
    refine nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _
      _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl,
      ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]

end GlobalTheory.SmGL.SwapBlocks
end
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.heisenberg_equivariant_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  first | exact @GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | exact GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | (intros; apply GlobalTheory.HeisenbergL2.map_dHeis_of_isometry <;> assumption)
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧ (∀ f, U 0 f = f) ∧ (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧ (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  first | exact @GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | exact GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | (intros; apply GlobalTheory.RealWeil.metaplectic_oneParam_schwartz <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz : ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  first | exact @GlobalTheory.RealWeil.tendsto_slope_omS_schwartz | exact GlobalTheory.RealWeil.tendsto_slope_omS_schwartz | (intros; apply GlobalTheory.RealWeil.tendsto_slope_omS_schwartz <;> assumption)
end
