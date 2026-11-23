module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.OpenCrit

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

def vOf (g : UG c (stdJ ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ * (mat c g).toBlocks₂₁

theorem lower_rel (g : UG c (stdJ ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ * ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

theorem vOf_herm (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]


open scoped Classical in
def nOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then unip c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := (weyl c ν)⁻¹ * nOf c g * weyl c ν

def pOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := g * (kOf c g)⁻¹

theorem nOf_mem (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem

theorem pOf_mem (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) : pOf c g ∈ sieg c ν := by
  rw [mem_sieg]
  have hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]
    rfl
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem continuous_mat : Continuous (mat c : UG c (stdJ ν E) → Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_blk₂₂ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem continuous_blk₂₁ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem blk₂₂_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, Matrix.one_apply]

theorem blk₂₁_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dif_pos hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end GlobalTheory.KSp.OpenCrit

namespace GlobalTheory.KSp


open OpenCrit in
theorem isOpen_of_sieg_of_opp (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end GlobalTheory.KSp
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.splitsInCMField_two_primes_degree_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPlace.split_place | exact GlobalTheory.CMVal.Euler.SplitPlace.split_place | (intros; apply GlobalTheory.CMVal.Euler.SplitPlace.split_place <;> assumption)
end

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

theorem Datum.finrank_La_ringOfIntegers :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
  haveI : IsScalarTower (𝓞 D.F) D.F D.VF :=
    ⟨fun c x v => by
      show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
      rw [mul_smul]⟩
  let f : D.La →ₗ[𝓞 D.F] D.VF :=
    { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
      map_add' := fun z w => TensorProduct.tmul_add _ _ _
      map_smul' := fun c z => by
        rw [RingHom.id_apply]
        show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
          algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
        rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
        rfl }
  have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

  have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
    intro n v
    show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : (c : D.F) ≠ 0 := by
        intro h
        exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
      rw [Module.End.isUnit_iff]
      constructor
      · intro v w h
        have h' : (c : D.F) • v = (c : D.F) • w := h
        exact smul_right_injective D.VF hc0 h'
      · intro v
        refine ⟨(c : D.F)⁻¹ • v, ?_⟩
        show (c : D.F) • ((c : D.F)⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · intro y
      obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
      have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
        mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
      refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
      show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
      rw [hnat, hf, hy]
      show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
      rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_one]
    · intro z w h
      rw [hf, hf] at h
      obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
        (TensorProduct.mk ℤ ℚ D.La 1)).1 h
      have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
        exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
      refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hcz
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
  have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
  rw [← h1, ← h2, D.finrank_VF]

end GlobalTheory.UPel.HT
end
end

section

open NumberField GlobalTheory.UPel.HT
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finrank_La_ringOfIntegers' :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  let : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have h : Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
    let : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
    have : IsScalarTower (𝓞 D.F) D.F D.VF :=
      ⟨fun c x v => by
        show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
        rw [mul_smul]⟩
    let f : D.La →ₗ[𝓞 D.F] D.VF :=
      { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
        map_add' := fun z w => TensorProduct.tmul_add _ _ _
        map_smul' := fun c z => by
          rw [RingHom.id_apply]
          show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
            algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
          rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
          rfl }
    have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

    have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
      intro n v
      show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
      rw [map_natCast, Nat.cast_smul_eq_nsmul]
    have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
      constructor
      · rintro ⟨c, hc⟩
        have hc0 : (c : D.F) ≠ 0 := by
          intro h
          exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
        rw [Module.End.isUnit_iff]
        constructor
        · intro v w h
          have h' : (c : D.F) • v = (c : D.F) • w := h
          exact smul_right_injective D.VF hc0 h'
        · intro v
          refine ⟨(c : D.F)⁻¹ • v, ?_⟩
          show (c : D.F) • ((c : D.F)⁻¹ • v) = v
          rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      · intro y
        obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
        have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
          mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
        refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
        show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
        rw [hnat, hf, hy]
        show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
        rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
          zsmul_eq_mul, mul_one]
      · intro z w h
        rw [hf, hf] at h
        obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
          (TensorProduct.mk ℤ ℚ D.La 1)).1 h
        have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
          exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
        refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
        show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
        rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact hcz
    have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
    have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
    rw [← h1, ← h2, D.finrank_VF]
  exact h
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.infinitesimal_point_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (exact GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (intros; apply GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.perfect_pairing_torsion_module : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (exact GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (intros; apply GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  first | exact @GlobalTheory.Obs.BasisO.restrict_bijective_one | exact GlobalTheory.Obs.BasisO.restrict_bijective_one | (intros; apply GlobalTheory.Obs.BasisO.restrict_bijective_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  first | exact @GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | exact GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | (intros; apply GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR

theorem cmpO_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    Function.Injective (cmpO s) := by
  intro R _ X s
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
  have hg' : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V),
      g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a) :=
    fun U V a ↦ congrFun (congrFun (congrFun hg U) V) a
  have ex : ∀ T : TT s, ∃ G : T.obj.B, ∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p :=
    fun T ↦ GlobalTheory.T.exists_glue_functions_spec_from_pairs T.obj.B (pt T) (hSec f g T) fun p q hpq ↦ GlobalTheory.T.cocycle_local_sections_restrict_compatibly f g hg' T p q hpq
  choose G hG using ex
  exact H1.mk_eq_zero.2 ⟨G, funext fun T ↦ funext fun T' ↦ funext fun φ ↦
    (GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued f g hg' φ (G T) (G T') (hG T) (hG T')).symm⟩

end GlobalTheory.CechDR
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) := by
  first | exact @GlobalTheory.NMulHom.isHom_nmul | exact GlobalTheory.NMulHom.isHom_nmul | (intros; apply GlobalTheory.NMulHom.isHom_nmul <;> assumption)
end
