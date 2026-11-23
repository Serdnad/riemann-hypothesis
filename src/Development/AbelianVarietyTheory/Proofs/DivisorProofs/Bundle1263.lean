module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Formalism.HarderNarasimhan.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem lift_left_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {h : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h₁ : h ≫ (fst G G).left = (fst G' G').left ≫ φ)
    (h₂ : h ≫ (snd G G).left = (snd G' G').left ≫ φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    {x y : T ⟶ G} {x' y' : T' ⟶ G'} (hx : x'.left ≫ φ = τ ≫ x.left) (hy : y'.left ≫ φ = τ ≫ y.left) :
    (lift x' y').left ≫ h = τ ≫ (lift x y).left := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_left_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    (hτ : τ ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = τ ≫ (1 : T ⟶ G).left := by
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  exact congrArg (fun q => q.left) ((map_one (pushHom hp T')).trans (MonObj.comp_one σ).symm)

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (B : Type) [CommRing B]

def twoMap [Algebra R B] : B ⊗[R] B →ₐ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight (R := K)).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ => .all _ _

theorem twoMap_tmul [Algebra R B] (a b : B) :
    twoMap (K := K) B (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [twoMap]

variable {B} [Bialgebra R B] [Module.Finite R B] [Module.Projective R B]

theorem contract_twoMap (χ : CartierDual R B) (u : B ⊗[R] B) :
    TensorProduct.rid K _ ((CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv.lTensor _ (twoMap (K := K) B u)) =
      (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ u) := by
  induction u with
  | add x y hx hy => simp only [map_add (f := _), hx, hy, tmul_add]
  | tmul a b =>
    have := CartierDual.baseChange_tmul_tmul K 1 1 χ b
    rw [twoMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rid_tmul, rid_tmul]
    rw [show (CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv ((1 : K) ⊗ₜ b) = χ.ofConv b • (1 * 1 : K) from this,
      _root_.mul_one, smul_assoc, one_smul, tmul_smul]

end Algebra

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

end Level

end GlobalTheory.WeilIntegral
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.SURankOneSeries

theorem term_even (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i) * q ^ (2 * i + 2 * (2 * i / 2)) = (z ^ 2) ^ i := by
  have h : 2 * i / 2 = i := by omega
  rw [h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]
  field_simp

theorem term_odd (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i + 1) * q ^ (2 * i + 1 + 2 * ((2 * i + 1) / 2)) = z / q * (z ^ 2) ^ i := by
  have h : (2 * i + 1) / 2 = i := by omega
  rw [h]
  have h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1 := by ring
  rw [h4]
  simp only [div_pow, ← pow_mul]
  rw [show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]
  field_simp
  ring

theorem hasSum_weighted (q z : ℂ) (hq : q ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) ((1 + q⁻¹ * z) / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hg := hasSum_geometric_of_norm_lt_one hz2
  have he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹ := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k :=
      funext fun k => term_even q z hq k
    rw [this]; exact hg
  have ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2)))
      (z / q * (1 - z ^ 2)⁻¹) := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) =
        fun k => z / q * (z ^ 2) ^ k := funext fun k => term_odd q z hq k
    rw [this]; exact hg.mul_left _
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    linarith
  have e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2) := by
    field_simp
  rw [← e]
  exact HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho

theorem hasSum_series : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  intro q hq z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hA := hasSum_weighted (q : ℂ) z hq0 hz
  set w : ℂ := z / (q : ℂ) ^ 2 with hw
  set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS
  set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha
  set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb
  have hB : HasSum b (w * S) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have e : (fun n => b (n + 1)) = fun n => w * a n := by
      funext n; simp [hb]
    rw [e]
    simpa [hb] using hA.mul_left w
  have hfun : (fun j : ℕ => w ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) =
      fun j => a j - b j := by
    funext j
    rcases j with _ | n
    · simp [ha, hb]
    · simp only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [pow_succ]; ring
  rw [hfun]
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  have e : cSU (q : ℂ) z = S - w * S := by
    rw [cSU, hS, hw]
    field_simp
  rw [e]
  exact hA.sub hB

end GlobalTheory.SURankOneSeries
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCell

section DiagConj

variable {L : Type} [Field L] {n : ℕ}

theorem gl_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    (D : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (D : Matrix (Fin n) (Fin n) L) i i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, hD i j h]

theorem gl_diag_ne_zero_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (D : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv D) i) i
  rw [gl_eq_diagonal_of_offdiag hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

theorem gl_inv_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    ((D⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ := by
  have hne := gl_diag_ne_zero_of_offdiag hD
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_left_inv
  calc Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) * (D : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
          Matrix.diagonal (fun i => (D : Matrix (Fin n) (Fin n) L) i i) :=
        congrArg _ (gl_eq_diagonal_of_offdiag hD)
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (hne i)

theorem gl_conj_apply_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (g : GL (Fin n) L) (i j : Fin n) :
    ((D⁻¹ * g * D : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ * (g : Matrix (Fin n) (Fin n) L) i j *
        (D : Matrix (Fin n) (Fin n) L) j j := by
  rw [Units.val_mul, Units.val_mul, gl_inv_eq_diagonal_of_offdiag hD]
  conv_lhs => rw [gl_eq_diagonal_of_offdiag hD]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem conj_mem_unipB_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipB L (Fin n)) : D⁻¹ * g * D ∈ unipB L (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem conj_mem_unipBLower_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipBLower L (Fin n)) : D⁻¹ * g * D ∈ unipBLower L (Fin n) := by
  rw [mem_unipBLower] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem weylRep_conj_offdiag {w : Equiv.Perm (Fin n)} {y t : GL (Fin n) L} (hy : IsWeylRep w y)
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → ((y⁻¹ * t * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have hyi := hy.inv
  rw [Units.val_mul, Units.val_mul, gl_eq_diagonal_of_offdiag ht, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = w j
  · subst hl
    rw [Matrix.mul_diagonal, hyi i (w j) (by simpa using hij), zero_mul, zero_mul]
  · rw [hy l j hl, mul_zero]

end DiagConj

end WeylCell

end GlobalTheory

end

theorem GlobalTheory.WeylCell.diagConjU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (y : GU σ n) (w : Equiv.Perm (Fin n)), IsWeylRep w (y : GL (Fin n) L) → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    IsBorelU (y⁻¹ * t * y) ∧ ∀ u ∈ cellU y, t⁻¹ * u * t ∈ cellU y := by
  intro L _ _ σ n y w hy t ht
  have hD := weylRep_conj_offdiag hy ht
  refine ⟨fun i j hij => ?_, fun u hu => ?_⟩
  · exact hD i j (ne_of_gt hij)
  · rw [cellU, Subgroup.mem_subgroupOf, mem_cell] at hu ⊢
    have e1 : (((t⁻¹ * u * t : GU σ n)) : GL (Fin n) L) =
        ((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L) := rfl
    rw [e1]
    refine ⟨conj_mem_unipB_of_offdiag ht hu.1, ?_⟩
    have e2 : ((y : GL (Fin n) L))⁻¹ * (((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L)) *
        (y : GL (Fin n) L) =
        ((y : GL (Fin n) L)⁻¹ * t * y)⁻¹ * ((y : GL (Fin n) L)⁻¹ * u * y) * ((y : GL (Fin n) L)⁻¹ * t * y) := by
      group
    rw [e2]
    exact conj_mem_unipBLower_of_offdiag hD hu.2
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.UnipShiftU

variable {L : Type} [Field L]

theorem unipB_mul_apply_succ {n : ℕ} {X Y : GL (Fin n) L} (hX : X ∈ unipB L (Fin n)) (hY : Y ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (Y : Matrix (Fin n) (Fin n) L) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

theorem unipB_inv_apply_succ {n : ℕ} {X : GL (Fin n) L} (hX : X ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = -(X : Matrix (Fin n) (Fin n) L) a a' := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have e := unipB_mul_apply_succ hX (inv_mem hX) h
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hne] at e
  linear_combination -e

theorem conj_apply {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (X : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * X * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * X (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro e; apply hb; rw [e]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem inv_mul_diag {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h : ((y⁻¹ * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i), Units.val_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rw [hy.inv i b (by intro e; apply hb; rw [e]; simp), zero_mul]
  · simp

theorem swap_inversion {n : ℕ} {a a' p q : Fin n} (h : a'.val = a.val + 1) (hpq : p < q)
    (hs : Equiv.swap a a' q < Equiv.swap a a' p) : p = a ∧ q = a' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at hs
  rw [Fin.lt_iff_val_lt_val] at hpq
  split_ifs at hs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem transvection_apply' {n : ℕ} (a a' : Fin n) (d : L) (i j : Fin n) :
    Matrix.transvection a a' d i j = (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

theorem ordL_one [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 := by
  unfold ordL
  rw [dite_eq_right (by simp)]
  simp
  rfl

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU
end
end

section

open NumberField IsDedekindDomain Matrix UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open UpperTheory.V.TR (infGL CuspSub)

namespace GlobalTheory.HenQ

theorem expo_eq_zero_of_pow {K : Type} [Field K] [NumberField K] [IsTotallyReal K] (ξ : Formalism.L2.Host.HChar K) {N : ℕ}
    (hN : 0 < N) (h : ξ ^ N = 1) (v : InfinitePlace K) : TR.expo ξ v = 0 := by
  classical
  have key : ∀ k : ℕ, ∀ z, TR.dchi (ξ ^ k) z = (k : ℂ) * TR.dchi ξ z := by
    intro k
    induction k with
    | zero => intro z; simp [TR.dchi_one]
    | succ k ih => intro z; rw [pow_succ, TR.dchi_mul, ih]; push_cast; ring
  have h1 := key N (Pi.single v 1)
  rw [h, TR.dchi_one] at h1
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  exact (mul_eq_zero.1 h1.symm).resolve_left hN'

end GlobalTheory.HenQ
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.gramDeterminant_smul_standardBasis_inverse_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  first | exact @GlobalTheory.DefPt.det_gramPl_smul_single | exact GlobalTheory.DefPt.det_gramPl_smul_single | (intros; apply GlobalTheory.DefPt.det_gramPl_smul_single <;> assumption)
end
