module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle041
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle027
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle038
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
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

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatProj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def entryEquiv (ι : Type) : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) where
  toFun X := fun kl => X kl.1 kl.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_entry (w : Matrix ι ι ℂ) (k : ι × ι) :
    (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = w k.1 k.2 := by
  rw [Module.Basis.ofEquivFun_repr_apply]; rfl

noncomputable def castLin (ι : Type) : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℂ where
  toFun X := X.map (algebraMap ℚ ℂ)
  map_add' X Y := by ext i j; simp
  map_smul' q X := by ext i j; simp [Rat.smul_def]

noncomputable def linExtLin (c : ι × ι → ι × ι → ℚ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := linExt c X
  map_add' X Y := by ext i j; simp [linExt, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [linExt, Finset.mul_sum, mul_left_comm]

theorem linExt_eq_sum (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (X : Matrix ι ι ℂ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) X =
      ∑ kl : ι × ι, X kl.1 kl.2 • castLin ι (p (single kl.1 kl.2 1)) := by
  ext i j
  simp [linExt, castLin, Matrix.sum_apply, mul_comm]

theorem linExt_cast (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (Y : Matrix ι ι ℚ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (castLin ι Y) = castLin ι (p Y) := by
  rw [linExt_eq_sum]
  have hY : Y = ∑ kl : ι × ι, Y kl.1 kl.2 • single kl.1 kl.2 (1 : ℚ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [Fintype.sum_prod_type]
    simp [Matrix.smul_single]
  conv_rhs => rw [hY]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [map_smul, map_smul]
  ext i j
  simp [castLin, Rat.smul_def]

theorem exists_rat_projector : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  intro ι _ _ E hE
  let E₀ : Submodule ℚ (Matrix ι ι ℚ) := (E.restrictScalars ℚ).comap (castLin ι)
  obtain ⟨π, hπ⟩ : ∃ π : Matrix ι ι ℚ →ₗ[ℚ] E₀, ∀ x : E₀, π x = x := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E₀.subtype E₀.ker_subtype
    exact ⟨g, fun x => LinearMap.congr_fun hg x⟩
  let p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ := E₀.subtype ∘ₗ π
  refine ⟨fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2, fun X => ?_, fun x hx => ?_⟩
  · rw [linExt_eq_sum]
    exact E.sum_mem fun kl _ => E.smul_mem _ (π (single kl.1 kl.2 1)).2
  · have hd := GlobalTheory.T.galoisStable_submodule_le_span_rational (Matrix ι ι ℂ) (ι × ι) (Module.Basis.ofEquivFun (entryEquiv ι)) E
      (fun σ w hw => ⟨w.map σ, hE σ w hw, fun k => by
        rw [repr_entry, repr_entry]; rfl⟩) hx
    have key : Set.EqOn (linExtLin fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (LinearMap.id (R := ℂ))
        {w | w ∈ E ∧ ∀ k, ∃ q : ℚ, (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = q} := by
      rintro w ⟨hw, hq⟩
      choose q hq using hq
      have hwq : w = castLin ι (Matrix.of fun i j => q (i, j)) := by
        ext i j
        have := hq (i, j)
        rw [repr_entry] at this
        simpa [castLin] using this
      have hmem : (Matrix.of fun i j => q (i, j)) ∈ E₀ := by
        change castLin ι _ ∈ E
        rw [← hwq]; exact hw
      have h1 : p (Matrix.of fun i j => q (i, j)) = Matrix.of fun i j => q (i, j) :=
        congrArg Subtype.val (hπ ⟨_, hmem⟩)
      have h2 := linExt_cast p (Matrix.of fun i j => q (i, j))
      rw [h1, ← hwq] at h2
      exact h2
    exact LinearMap.eqOn_span key hd

end GlobalTheory.ClassFin.RatProj
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Gen

end GlobalTheory.UTrans.Gen

namespace GlobalTheory.UTrans

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem refl_eq_tv_sub_one_div_hf {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    _root_.GlobalTheory.UnRep.refl c G x u =
      _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((u - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
    _root_.GlobalTheory.UTrans.Model.tv_mulVec]
  change v + ((u - 1) * _root_.GlobalTheory.UTrans.hf (c : E →+* E) G v x /
    _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) • x = _
  congr 2
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem det_refl_eq_of_hermE_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E)
    (hx : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0) :
    (_root_.GlobalTheory.UnRep.refl c G x u).det = u := by
  unfold _root_.GlobalTheory.UnRep.refl
  have hw : (G.mulVec fun b => c (x b)) ⬝ᵥ x = _root_.GlobalTheory.UnRep.hermE c G x x :=
    (_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot c G x x).symm
  have hmat : ((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) •
      Matrix.vecMulVec x (G.mulVec fun b => c (x b)) =
      Matrix.replicateCol Unit (((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) • x) *
        Matrix.replicateRow Unit (G.mulVec fun b => c (x b)) := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hw, smul_eq_mul]
  field_simp
  ring


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.UTrans.isU_eq_tv_mul_tvGen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ γ, _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G γ → (∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G) := by
  intro F E _ _ _ _ _ c n G hG hiso γ hγ
  have hG' : _root_.GlobalTheory.UnRep.IsHermForm c G := by
    refine ⟨hG.invol, ?_, hG.herm,
      hG.det_ne⟩
    intro h1
    obtain ⟨a, ha⟩ := hG.ne_id
    apply ha
    rw [h1]
    rfl
  have hγ' : _root_.GlobalTheory.UnRep.IsUnE c G γ := fun v w => hγ v w
  obtain ⟨l, hl, hγl⟩ := _root_.GlobalTheory.UnRep.isUnE_eq_prod_refl F E c n G hG' γ hγ'
  have hnorm := (_root_.GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG).2
  have main : ∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 →
      ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G,
        γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x
          ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m := by
    intro x hx
    have hx' : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 := hx
    obtain ⟨_, _, hmul, hunit⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'

    have key : ∀ l' : List ((Fin n → E) × E),
        (∀ p ∈ l', _root_.GlobalTheory.UnRep.hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
        ∃ M ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, ∃ U : E, U * c U = 1 ∧
          (l'.map fun p => _root_.GlobalTheory.UnRep.refl c G p.1 p.2).prod =
            M * _root_.GlobalTheory.UnRep.refl c G x U := by
      intro l' hl'
      induction l' with
      | nil =>
        refine ⟨1, Submonoid.one_mem _, 1, by simp, ?_⟩
        obtain ⟨_, h1, _, _⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'
        simp [h1]
      | cons p l' ih =>
        obtain ⟨M, hM, U, hU, hprod⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        obtain ⟨hp1, hp2⟩ := hl' p List.mem_cons_self
        obtain ⟨m₁, hm₁, hq₁⟩ := _root_.GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul E n (c : E →+* E) G hG hiso
          p.1 x p.2 hp1 hx hp2
        obtain ⟨M', hM', hcomm, _⟩ := (hnorm M hM).2.2.2 _ ((hunit p.2 hp2) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
        refine ⟨m₁ * M', Submonoid.mul_mem _ hm₁ hM', p.2 * U, ?_, ?_⟩
        · rw [map_mul]
          calc p.2 * U * (c p.2 * c U) = (p.2 * c p.2) * (U * c U) := by ring
            _ = 1 := by rw [hp2, hU, one_mul]
        · rw [List.map_cons, List.prod_cons, hprod, refl_eq_tv_sub_one_div_hf, hq₁,
            ← refl_eq_tv_sub_one_div_hf, ← hmul]
          calc m₁ * _root_.GlobalTheory.UnRep.refl c G x p.2 * (M * _root_.GlobalTheory.UnRep.refl c G x U)
              = m₁ * (_root_.GlobalTheory.UnRep.refl c G x p.2 * M) * _root_.GlobalTheory.UnRep.refl c G x U := by
                simp only [mul_assoc]
            _ = m₁ * (M' * _root_.GlobalTheory.UnRep.refl c G x p.2) * _root_.GlobalTheory.UnRep.refl c G x U := by
                rw [hcomm]
            _ = _ := by simp only [mul_assoc]
    obtain ⟨M, hM, U, hU, hprod⟩ := key l hl
    have hγM : γ = M * _root_.GlobalTheory.UnRep.refl c G x U := hγl.trans hprod
    have hdet : γ.det = U := by
      rw [hγM, Matrix.det_mul, (hnorm M hM).2.1, one_mul, det_refl_eq_of_hermE_ne_zero c G x U hx']
    obtain ⟨_, _, _, m'', hm'', hcomm⟩ := (hnorm M hM).2.2.2 _ ((hunit U hU) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
    refine ⟨m'', hm'', ?_⟩
    rw [hdet, hγM, hcomm, refl_eq_tv_sub_one_div_hf]
  refine ⟨main, fun h1 => ?_⟩
  obtain ⟨z, hz, _⟩ := hiso
  obtain ⟨i, -⟩ := Function.ne_iff.mp hz
  obtain ⟨y, hyy, -, -⟩ := _root_.GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG'
  obtain ⟨m, hm, hγm⟩ := main (y i) (hyy i)
  have h0 : _root_.GlobalTheory.UTrans.tv (c : E →+* E) G (y i) 0 = 1 := by
    unfold _root_.GlobalTheory.UTrans.tv
    ext a b
    simp
  rw [h1, sub_self, zero_div, h0, one_mul] at hγm
  rw [hγm]
  exact hm

end GlobalTheory.UTrans
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem isSquare_real_iff_nonneg (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun h => h.nonneg, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩

theorem index_sqSub_real_dvd_two {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by
  by_cases h : ∀ x : Fˣ, x ∈ sqSub σ
  · rw [show sqSub σ = ⊤ from eq_top_iff.mpr fun x _ => h x, Subgroup.index_top]
    exact one_dvd 2
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have hne : ∀ x : Fˣ, σ (x : F) ≠ 0 := fun x => (x.isUnit.map σ).ne_zero
    have hmem : ∀ x : Fˣ, x ∈ sqSub σ ↔ 0 ≤ σ (x : F) := fun x =>
      (mem_sqSub σ x).trans (isSquare_real_iff_nonneg _)
    have ha' : σ (a : F) < 0 := not_le.mp fun h' => ha ((hmem a).mpr h')
    have h2 : (sqSub σ).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      rw [hmem, hmem, Units.val_mul, map_mul]
      rcases lt_or_gt_of_ne (hne b) with hb | hb
      · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hb.le ha'.le, not_le.mpr hb⟩
      · exact Or.inr ⟨hb.le, not_le.mpr (mul_neg_of_pos_of_neg hb ha')⟩
    rw [h2]

theorem exists_valuation_two_eq_exp {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ e : ℕ, v.valuation F 2 = WithZero.exp (-(e : ℤ)) := by
  have h2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
  have hle : v.valuation F 2 ≤ 1 := by
    rw [h2]
    exact v.valuation_le_one 2
  have hne : v.valuation F 2 ≠ 0 := (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hk : WithZero.log (v.valuation F 2) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log (v.valuation F 2)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

private theorem index_biInf_ne_zero_and_le_prod {G ι : Type} [Group G] [DecidableEq ι] (S : Finset ι)
    (f : ι → Subgroup G) :
    (∀ i ∈ S, (f i).index ≠ 0) →
      (⨅ i ∈ S, f i).index ≠ 0 ∧ (⨅ i ∈ S, f i).index ≤ ∏ i ∈ S, (f i).index := by
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    obtain ⟨h0, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 := hf a (Finset.mem_insert_self a s)
    exact ⟨Subgroup.index_inf_ne_zero ha0 h0,
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hle)⟩

theorem index_locSq_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  classical
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_two_eq_exp v
  have hP := GlobalTheory.T.prod_absNorm_pow_valuation_two_le F S e (fun v _ => he v)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e v :=
    fun v => GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le F v (e v) (he v)
  obtain ⟨hF0, hFle⟩ := index_biInf_ne_zero_and_le_prod S (fun v => sqSub (algebraMap F (v.adicCompletion F)))
    (fun v _ => (hN v).1)
  have hR2 : ∀ σ : F →+* ℝ, (sqSub σ).index ≤ 2 := fun σ =>
    Nat.le_of_dvd two_pos (index_sqSub_real_dvd_two σ)
  obtain ⟨hR0, hRle⟩ := index_biInf_ne_zero_and_le_prod (Finset.univ : Finset (F →+* ℝ)) (fun σ => sqSub σ)
    (fun σ _ => ne_zero_of_dvd_ne_zero two_ne_zero (index_sqSub_real_dvd_two σ))
  have hRu : (⨅ σ : F →+* ℝ, sqSub σ) = ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    simp
  have hloc : locSq F S = (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))) ⊓
      ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    rw [← hRu]
    rfl
  rw [hloc]
  refine ⟨Subgroup.index_inf_ne_zero hF0 hR0, ?_⟩
  have hF : (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))).index ≤
      4 ^ S.card * 2 ^ Module.finrank ℚ F := by
    refine hFle.trans ?_
    calc ∏ v ∈ S, (sqSub (algebraMap F (v.adicCompletion F))).index
        ≤ ∏ v ∈ S, (4 * Ideal.absNorm v.asIdeal ^ e v) :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun v _ => (hN v).2)
      _ = 4 ^ S.card * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 4 ^ S.card * 2 ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ hP
  have hR : (⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ).index ≤
      2 ^ InfinitePlace.nrRealPlaces F := by
    refine hRle.trans ?_
    calc ∏ σ ∈ (Finset.univ : Finset (F →+* ℝ)), (sqSub σ).index
        ≤ ∏ _σ ∈ (Finset.univ : Finset (F →+* ℝ)), 2 :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun σ _ => hR2 σ)
      _ = 2 ^ InfinitePlace.nrRealPlaces F := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' F]
  refine Subgroup.index_inf_le.trans ((Nat.mul_le_mul hF hR).trans (le_of_eq ?_))
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, show (4 : ℕ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

end GlobalTheory.QNorm
end
