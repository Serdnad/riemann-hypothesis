module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ContinuousMhUInv
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


open PositivityTheory.ThKF0.Resc in

theorem split_core {m n : ℕ} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ : E}
    (hq : IsQuad σ δ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (hA : IsHerm σ JA)
    (hB : IsHerm σ JB)
    (d' : Darboux (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB))) κ)
    (d₀ : Matrix (Fin m) (Fin n ⊕ Fin n) E ≃ₗ[F] (κ → F) × (κ → F))
    (hd : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)))
    (χ : Chr F E) (hχ : IsHecke F E χ)
    (om' : UG (cA σ) (incM F (dbl JB)) →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ d' (actB (cA σ)) om')
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB)) d' χ
      (diagCols (Fin n)) om')
    (g : UG (cA σ) (incM F (dbl JB)))
    (hg : ∃ γ₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E,
      ((g : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F γ₀) :
    ∀ Ψ ∈ schA F κ, thetaSum F (om' g Ψ) = thetaSum F Ψ := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hL : IsLagr σ (dbl JB) (diagCols (Fin n)) := isLagr_diagCols (R := F) σ JB
  have hC : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map
      (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = diagCols (Fin n) := by
    have e1 : (1 : Matrix (Fin n) (Fin n) E).map (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = 1 :=
      Matrix.map_one _ (map_zero (inclR (F := F) (AF F))) (map_one (inclR (F := F) (AF F)))
    simp only [diagCols, Matrix.fromRows_map, e1]
  have hχ' : ∀ (z : E) (u : (AE F E)ˣ), (u : AE F E) = (1 : AF F) ⊗ₜ[F] z → χ u = 1 := fun z u hu => by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
      (algebraMap F (AF F)).injective).nontrivial
    have hz : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
    rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
    exact hχ.2 _
  exact GlobalTheory.CompanionTheory.ThetaMember.split_of_eq F E σ δ (Fin m) (Fin n ⊕ Fin n) κ JA (dbl JB)
    ψ hψ.1 (PositivityTheory.ThKF0.isStd_ne_one hψ) hψ.2.1 hq hA (GlobalTheory.CompanionTheory.ThetaMember.isHerm_dbl hB)
    (incM F (dbl JB)) rfl d' d₀ hd χ (Fin n) (diagCols (Fin n)) (diagCols (Fin n)) hC om' hχ' hL hS hR g hg


omit [NumberField F] [NumberField E] in
theorem split_resc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] [Invertible (2 : R)] {c : K →ₐ[R] K}
    {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
    {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {C : TestClass R} {ψ : AddChar R ℂ} {d : Darboux (symp c ξ JA JB) κ}
    {χ : Kˣ →* Circle} {Cy : Matrix β ν K} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hS : IsSplitting C ψ d (actB c) om) (hR : SiegelRule c C ψ ξ JA JB d χ Cy om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsSplitting C ψ d' (actB c) om' ∧ SiegelRule c C ψ ξ' JA' JB' d' χ Cy om' ∧
      ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  have hU : UG c (v • JB) = UG c JB := PositivityTheory.ThKF0.Resc.ug_smul hv JB
  refine ⟨⟨d.e, fun w w' => (PositivityTheory.ThKF0.Resc.symp_smul h JA JB w w').trans (d.form w w')⟩,
    om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
    fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hU.le p) t hp,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩


open PositivityTheory.ThKF0.Resc in

theorem theta_sum_rational_invariant (d : SD σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil

  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1

  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat

  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ

end PositivityTheory.SiegelWeilFormula.Tauto

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem countable_E : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_mat (p q : ℕ) : Countable (Matrix (Fin p) (Fin q) E) := by
  haveI := countable_E (E := E)
  exact inferInstanceAs (Countable (Fin p → Fin q → E))

def tr (d : SD σ) (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E) : Mx F E d.m d.n := mat g⁻¹ * incM F X

theorem cont_tr (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    Continuous fun g : UA σ d.A.J => f (tr d g X) := by
  have h1 : Continuous (f ∘ d.cmb) := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [Kdil.Tb.cmb_crd]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [tr, e, Kdil.Tb.crd_mul]
  exact h1.comp (((Kdil.Tb.continuous_mh d).comp h2).matrix_mulVec continuous_const)

theorem chr_comb (d : SD σ) (β G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [SD.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add (f := _), map_smul, smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring

theorem half_eq_iff (d : SD σ) (G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2

end PositivityTheory.SiegelWeilFormula.Tauto

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem thetaSum_S_rat (hP : TPar) (hT : TTheta) (d : SD σ) {γ : UA σ d.A.J} (hγ : γ ∈ ratU σ d.A.J)
    {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : thetaSum F (d.S γ Ψ) = thetaSum F Ψ := by
  have hS : d.S γ Ψ ∈ d.sch := d.ok.dbl.lin.pres γ Ψ hΨ
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)
  obtain ⟨g₁, hg₁⟩ := PositivityTheory.ThKF0.Resc.rat_mat hγ
  have hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    PositivityTheory.SiegelWeilFormula.kfour.incM_injective
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E),
      incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))
  have hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e01 : g₀ * g₁ = 1 := hinj (by
    rw [hmul, ← hg₀, ← hg₁, hone]
    have := congrArg (fun u : UA σ d.A.J => ((u.1 : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)))
      (inv_mul_cancel γ)
    simp at this; simpa using this)
  have e10 : g₁ * g₀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    ⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc, e01]⟩
  have h1 := (hT F E σ d (d.S γ Ψ) hS).1
  have h2 := (hT F E σ d Ψ hΨ).1
  have h3 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ)) := by
    refine h1.congr_fun fun X => ?_
    rw [(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]
    simp only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]
  exact h3.unique ((e.hasSum_iff).2 h2)

end PositivityTheory.SiegelWeilFormula.Tauto

end
end
