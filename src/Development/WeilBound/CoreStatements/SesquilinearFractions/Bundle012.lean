module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle004
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle011
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  intro E _ _ M _ _ _ _ I _ ℓ hℓ hcard
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (𝓞 E) ℓ (M := M) hℓ
  let e : I ≃ Fin (Module.finrank (𝓞 E) M) := Fintype.equivFinOfCardEq hcard
  refine ⟨b ∘ e, hb.1.comp e e.injective, ?_⟩
  obtain ⟨n, hn, hsp⟩ := hb.2
  refine ⟨n, hn, fun y => ?_⟩
  have : Set.range (b ∘ e) = Set.range b := e.surjective.range_comp b
  rw [this]
  exact hsp y

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

theorem models (X : CMPack Z c FU i hP) :
    ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)),
      M.IsActOf Xo.univ.t.act.act ρ ∧
      ∃ (M1 : LieModel X.t.G (𝟙 (Sp X.K)) (Fin g → X.K))
        (M2 : LieModel X.B.t.G (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin g → X.K)),
        (∀ e, (M1.pt e).left ≫ X.m.φ = (M.pt e).left) ∧ (∀ e, (M1.pt e).left ≫ X.m'.φ = (M2.pt e).left) := by
  obtain ⟨n, M, ρ, hρ, -⟩ := GlobalTheory.T.lie_model_action_base_change E H Xo.X Xo.univ.t X.K (under X.y)
  have h1 : under X.y = 𝟙 (Sp X.K) ≫ under X.y := by simp
  obtain ⟨M1, hM1⟩ := (GlobalTheory.T.lie_model_pullback_equivalence Xo.X (Sp X.K) Xo.univ.t.G X.t.G (under X.y) X.m.φ X.m.cart X.K (𝟙 _)
    (Fin n → X.K)).1 (castM h1 M)
  obtain ⟨M2, hM2⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp (𝓞 X.K)) (Sp X.K) X.B.t.G X.t.G (spMap (algebraMap (𝓞 X.K) X.K)) X.m'.φ
    X.m'.cart X.K (𝟙 _) (Fin n → X.K)).2 M1
  obtain ⟨bas⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp (𝓞 X.K)) X.B.t.G g (by have hd := X.B.dim; rwa [X.dim] at hd) X.K
    (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin n → X.K) M2
  have hn : n = g := by
    have := Module.finrank_eq_card_basis bas
    simpa using this
  subst hn
  exact ⟨M, ρ, hρ, M1, M2, fun e => (hM1 e).trans (castM_left h1 M e), hM2⟩

end PositivityTheory.Xgf.cm_lie_model_action

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rank_free_prod (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (p : ℕ) :
    Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L) = p + Module.rank (𝓞 E) L := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst (𝓞 E) (Fin p → 𝓞 E) L)
  rw [LinearMap.range_eq_top_of_surjective _ LinearMap.fst_surjective, rank_top, rank_fin_fun,
    LinearMap.ker_fst] at h
  rw [← h, ← (LinearEquiv.ofInjective (LinearMap.inr (𝓞 E) (Fin p → 𝓞 E) L)
    LinearMap.inr_injective).rank_eq]

theorem family_orthogonal_sum_injective (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0)
    (c : Fin p → 𝓞 E) (z : orthogonalFamilyAlt D x') (h : familyCombination D x' c + (z : D.La) = 0) : c = 0 ∧ z = 0 := by
  have hadd : ∀ u v w : D.La, sesq D u (v + w) = sesq D u v + sesq D u w := by
    intro u v w
    simp only [sesq, map_add (f := _), Int.cast_add, add_mul, Finset.sum_add_distrib]
  have hcomb : familyCombination D x' c = ∑ a, c a • x' a := rfl
  have hv : (gramE D x') *ᵥ (fun a => IsCMField.complexConj E ((c a : 𝓞 E) : E)) = 0 := by
    funext b
    have hb := congrArg (sesq D (x' b)) h
    have h0 : sesq D (x' b) 0 = 0 := by simp [sesq]
    have hz : sesq D (x' b) (z : D.La) = 0 := z.2 b
    rw [hadd, hcomb, sesq_integral_combination, hz, h0, _root_.add_zero] at hb
    simpa [Matrix.mulVec, dotProduct] using hb
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hc : c = 0 := by
    funext a
    have ha := congrFun hc0 a
    simp only [Pi.zero_apply, map_eq_zero] at ha
    first
      | simpa using ha
      | exact RingOfIntegers.coe_eq_zero_iff.mp ha
      | exact_mod_cast ha
  refine ⟨hc, ?_⟩
  subst hc
  have h1 : familyCombination D x' 0 = 0 := map_zero _
  rw [h1, _root_.zero_add] at h
  exact Submodule.coe_eq_zero.mp h

theorem finrank_orthogonal_family (D : Datum H) {p q : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a) :
    Module.finrank (𝓞 E) (orthogonalFamilyAlt D x') = q := by
  classical
  haveI := D.fin
  set L2 := orthogonalFamilyAlt D x' with hL2
  let ψ : ((Fin p → 𝓞 E) × L2) →ₗ[𝓞 E] D.La := (familyCombination D x').coprod L2.subtype
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨c, z⟩ h
    obtain ⟨hc, hz⟩ := family_orthogonal_sum_injective D x' hdet c z h
    rw [hc, hz]
    rfl
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  let φ : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) × L2 :=
    (integralCoeffs D x' m hm).prod
      ((orthogonalComponent D x' m hm).codRestrict L2 (fun y => orthogonalComponent_mem D x' m hm hdet y))
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : integralCoeffs D x' m hm y = 0 := congrArg Prod.fst hy
    have h2 : orthogonalComponent D x' m hm y = 0 := by
      have h3 := congrArg (fun w => (w.2 : D.La)) hy
      simpa [φ] using h3
    rw [hyp, h1, map_zero, sub_zero] at h2
    exact nsmul_injective_lattice D hm0 (by rw [h2, smul_zero])
  have hr : Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L2) = Module.rank (𝓞 E) D.La :=
    le_antisymm (LinearMap.rank_le_of_injective ψ hψ) (LinearMap.rank_le_of_injective φ hφ)
  rw [rank_free_prod, ← Module.finrank_eq_rank (𝓞 E) D.La, D.rank, ← hpq,
    ← Module.finrank_eq_rank (𝓞 E) L2] at hr
  norm_cast at hr
  omega

theorem exists_orthogonal_local_basis_extension (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧
      ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  classical
  obtain ⟨m, hmℓ, hm⟩ := exists_common_denominator_coeffs D x' ℓ hdet hlog
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmℓ (dvd_zero _)
  haveI := D.fin
  haveI := D.proj
  set L2 := orthogonalFamilyAlt D x' with hL2
  have hfr : Module.finrank (𝓞 E) L2 = q := finrank_orthogonal_family D x' ℓ hpq hdet m hm0 hm
  obtain ⟨b0, hb0⟩ := exists_local_basis_cm_order.locBasis' (𝓞 E) (ℓ : ℕ) ℓ.prop (M := L2)
  let b : Fin q → L2 := b0 ∘ Fin.cast hfr.symm
  have hbli : LinearIndependent (𝓞 E) b := hb0.1.comp _ (Fin.cast_injective _)
  obtain ⟨n, hnℓ, hn⟩ := hb0.2
  have hrange : Set.range b = Set.range b0 := Function.Surjective.range_comp (fun i => ⟨Fin.cast hfr i, by ext; simp⟩) _
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  refine ⟨Sum.elim x' (fun j => (b j : D.La)), rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    set z : L2 := ∑ j, g (Sum.inr j) • b j with hz
    have hzc : (z : D.La) = ∑ j, g (Sum.inr j) • (b j : D.La) := by simp [hz]
    have hpsi := family_orthogonal_sum_injective D x' hdet (fun a => g (Sum.inl a)) z (by rw [hzc]; exact hg)
    have hg2 : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.mp hbli _ hpsi.2
    rintro (a | j)
    · exact congrFun hpsi.1 a
    · exact hg2 j
  · refine ⟨m * n, ?_, ?_⟩
    · rw [ℓ.prop.dvd_mul]
      push_neg
      exact ⟨hmℓ, hnℓ⟩
    · intro y
      have hdec : m • y = familyCombination D x' (integralCoeffs D x' m hm y) + orthogonalComponent D x' m hm y := by
        rw [hyp]
        abel
      rw [_root_.mul_comm m n, mul_smul, hdec, smul_add]
      apply Submodule.add_mem
      · apply nsmul_mem
        show ∑ a, integralCoeffs D x' m hm y a • x' a ∈ _
        refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩))
      · have h1 := hn ⟨_, orthogonalComponent_mem D x' m hm hdet y⟩
        rw [← hrange] at h1
        have h2 := Submodule.mem_map_of_mem (f := L2.subtype) h1
        rw [Submodule.map_span] at h2
        have h3 := Submodule.span_mono (R := 𝓞 E) (s := L2.subtype '' Set.range b)
          (t := Set.range (Sum.elim x' (fun j => (b j : D.La)))) (by
            rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
            exact ⟨Sum.inr j, rfl⟩) h2
        simpa using h3
  · intro a j
    exact (b j).2 a

end GlobalTheory.CompanionTheory.Ar.Fl

end

namespace PositivityTheory.Xgf

theorem exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 :=
  fun _ _ _ _ _ D p q ℓ x' hpq hdet hlog => GlobalTheory.CompanionTheory.Ar.Fl.exists_orthogonal_local_basis_extension D p q ℓ x' hpq hdet hlog

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

def Hm : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k k' => if ty k = ty k' then 2 * Complex.I * ty k (G (blk hty k) (blk hty k')) else 0

def Q (σ : E →+* ℂ) (z w : Fin g → ℂ) : ℂ :=
  ∑ k : {k // ty k = σ}, ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k')

theorem herm_split (z w : Fin g → ℂ) : hermForm (Hm hty G) z w = ∑ σ, Q hty G σ z w := by
  have hF : ∀ σ : E →+* ℂ, ∀ k : {k // ty k = σ},
      ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k') =
      z k * (Hm hty G *ᵥ star w) k := by
    intro σ ⟨k, hk⟩
    simp only [mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype (fun k' => ty k' = σ)]
    have h2 : ∑ k' : {k' // ¬ ty k' = σ}, z k * (Hm hty G k k' * conj (w k')) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨k', hk'⟩ _
      have hne : ¬ ty k = ty k' := by
        rw [hk]
        exact fun h => hk' h.symm
      simp [Hm, hne]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    rintro ⟨k', hk'⟩ _
    have heq : ty k = ty k' := hk.trans hk'.symm
    simp only [Hm, Matrix.of_apply, heq, if_true]
    rw [hk']
    ring
  unfold hermForm
  rw [dotProduct, ← Fintype.sum_fiberwise ty]
  apply Finset.sum_congr rfl
  intro σ _
  unfold Q
  apply Finset.sum_congr rfl
  intro k _
  exact (hF σ k).symm

theorem Q_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin p, ∑ b : Fin p, z ((eP hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inl a) (.inl b))) * conj (w ((eP hty σ h).symm b)) := by
  have hb : ∀ a : Fin p, blk hty ((eP hty σ h).symm a : Fin g) = Sum.inl a := by
    intro a
    rw [blk_inl hty σ h _ ((eP hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

theorem Q_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin q, ∑ b : Fin q, z ((eQ hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inr a) (.inr b))) * conj (w ((eQ hty σ h).symm b)) := by
  have hb : ∀ a : Fin q, blk hty ((eQ hty σ h).symm a : Fin g) = Sum.inr a := by
    intro a
    rw [blk_inr hty σ h _ ((eQ hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

end PositivityTheory.Xgf.DPer

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem principal_root_re_zero_im_sq : H.rt0.re = 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [sq] at h1 h2
  by_contra h0
  have : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  rw [this] at h1
  nlinarith [mul_self_nonneg H.rt0.re]

theorem rt0_conj_neg_ne_zero : conj H.rt0 = -H.rt0 := by
  apply Complex.ext <;> simp [principal_root_re_zero_im_sq (H := H)]

theorem conjugate_rt (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 ↔ σ (H.rt : E) ≠ H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases rt_cases (H := H) σ with h | h
  · rw [h, rt0_conj_neg_ne_zero]
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    simp only [true_iff]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm

theorem sum_split {M : Type} [AddCommMonoid M] (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F σ +
      ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F (ComplexEmbedding.conjugate σ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0)]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (conjugate_rt σ).2 hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact fun h' => ((conjugate_rt σ).1 h') hσ
  · intro σ _; ext x; simp
  · intro σ _; ext x; simp
  · intro σ _; simp

theorem emb_indep (l : (E →+* ℂ) → ℂ) (h : ∀ b : 𝓞 E, ∑ σ, l σ * σ (b : E) = 0) : l = 0 := by
  let F : (E →+* ℂ) → (𝓞 E →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hF : Function.Injective F := by
    intro σ σ' e
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext b
    exact DFunLike.congr_fun e b
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp F hF
  funext σ
  refine Fintype.linearIndependent_iff.1 li l ?_ σ
  funext b
  simpa [F, Finset.sum_apply] using h b

theorem exists_big (a : 𝓞 E) (ha : a ≠ 0) (b : Bool) :
    ∃ σ : E →+* ℂ, σ (H.rt : E) = (if b then H.rt0 else -H.rt0) ∧ 1 ≤ ‖σ (a : E)‖ := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    intro σ
    by_cases hσ : σ (H.rt : E) = (if b then H.rt0 else -H.rt0)
    · exact hcon σ hσ
    · have h2 : ComplexEmbedding.conjugate σ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
        rw [ComplexEmbedding.conjugate_coe_eq]
        rcases rt_cases (H := H) σ with h | h <;> cases b <;>
          simp_all [rt0_conj_neg_ne_zero (H := H)]
      have := hcon _ h2
      rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at this
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hlt : ∏ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ₀)]
    have h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun σ _ => (hall σ).le)
    calc ‖σ₀ (a : E)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ ‖σ₀ (a : E)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rw [_root_.mul_one]; exact hall σ₀
  have hge : 1 ≤ ∏ σ : E →+* ℂ, ‖σ (a : E)‖ := by
    have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
    have e1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : E)
    rw [← Algebra.coe_norm_int] at e1
    have e2 : ∏ τ : E →ₐ[ℚ] ℂ, τ (a : E) = ∏ σ : E →+* ℂ, σ (a : E) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun τ => rfl)
    rw [e2] at e1
    rw [← norm_prod, ← e1]
    have : ((algebraMap ℚ ℂ) ((Algebra.norm ℤ a : ℤ) : ℚ)) = ((Algebra.norm ℤ a : ℤ) : ℂ) := by simp
    rw [this, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN
  linarith

end PositivityTheory.Xgf.DPer

end
end
