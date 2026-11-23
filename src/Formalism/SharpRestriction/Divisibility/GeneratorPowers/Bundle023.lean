module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasis
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix

namespace GramSpaceAlt

def GramSp (ι : Type) : Type := ι → ℝ

instance (ι : Type) : AddCommGroup (GramSp ι) := inferInstanceAs (AddCommGroup (ι → ℝ))
instance (ι : Type) : Module ℝ (GramSp ι) := inferInstanceAs (Module ℝ (ι → ℝ))
instance (ι : Type) [Fintype ι] : FiniteDimensional ℝ (GramSp ι) :=
  inferInstanceAs (FiniteDimensional ℝ (ι → ℝ))

def toG (ι : Type) : (ι → ℝ) ≃ₗ[ℝ] GramSp ι := LinearEquiv.refl ℝ (ι → ℝ)

def gBasis (ι : Type) [Fintype ι] [DecidableEq ι] : Basis ι ℝ (GramSp ι) := (Pi.basisFun ℝ ι).map (toG ι)

@[instance_reducible]
def gramCore {ι : Type} [Fintype ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) : InnerProductSpace.Core ℝ (GramSp ι) where
  inner x y := dotProduct ((toG ι).symm x) (G *ᵥ (toG ι).symm y)
  conj_inner_symm x y := by
    have hT : Gᵀ = G := by
      have h := hG.1
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simp only [conj_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  re_inner_nonneg x := by
    simp only [RCLike.re_to_real]
    by_cases hx : (toG ι).symm x = 0
    · rw [hx, zero_dotProduct]
    · have h := hG.dotProduct_mulVec_pos hx
      rw [star_trivial] at h
      exact h.le
  add_left x y z := by simp only [map_add (f := _), add_dotProduct]
  smul_left x y r := by simp only [map_smul, smul_dotProduct, conj_trivial, smul_eq_mul]
  definite x h := by
    by_contra hx
    have hx' : (toG ι).symm x ≠ 0 := fun h0 => hx (by simpa using congrArg (toG ι) h0)
    have h2 := hG.dotProduct_mulVec_pos hx'
    rw [star_trivial] at h2
    exact h2.ne' h

end GramSpaceAlt

open GramSpaceAlt

theorem gram_form_phi_holds : GramFormPhiStatement := by
  classical
  intro E _ _ cj hcj hcm w₀ hw₀ Y _ _ _ _ β hpos
  obtain ⟨v, hv, hvb⟩ := phiCMinima_holds E cj hcj hcm w₀ hw₀ Y β hpos
  obtain ⟨ι, hι, b0, hG⟩ := hpos
  let _ := hι
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hBdef
  set G : Matrix ι ι ℝ := Matrix.of fun i j => B (b0 i) (b0 j) with hGdef
  let cd : InnerProductSpace.Core ℝ (GramSp ι) := gramCore G hG
  let _ : NormedAddCommGroup (GramSp ι) := @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ cd
  let _ : InnerProductSpace ℝ (GramSp ι) := InnerProductSpace.ofCore cd.toCore

  let ψ0 : Y →ₗ[ℤ] (ι → ℝ) :=
    { toFun := fun y i => (b0.repr y i : ℝ)
      map_add' := fun y z => by funext i; simp
      map_smul' := fun c y => by funext i; simp }
  let ψ : Y →ₗ[ℤ] GramSp ι := ((toG ι).toLinearMap.restrictScalars ℤ).comp ψ0
  have hψ_apply : ∀ y, (toG ι).symm (ψ y) = ψ0 y := fun y => rfl

  have key : ∀ y z, B y z = ∑ i, ∑ j, (b0.repr y i : ℝ) * ((b0.repr z j : ℝ) * B (b0 i) (b0 j)) := by
    intro y z
    rw [← LinearMap.sum_repr_mul_repr_mul b0 b0 (B := B) y z, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zsmul_eq_mul]
  have hin : ∀ y z, inner ℝ (ψ y) (ψ z) = B y z := by
    intro y z
    rw [key]
    change dotProduct (ψ0 y) (G *ᵥ ψ0 z) = _
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk, hGdef, Matrix.of_apply]
    ring
  have hnorm : ∀ y, ‖ψ y‖ ^ 2 = B y y := fun y => by
    rw [← real_inner_self_eq_norm_sq, hin]

  have hψX : ∀ y, ψ y ∈ Submodule.span ℤ (Set.range (gBasis ι)) := by
    intro y
    rw [(gBasis ι).mem_span_iff_repr_mem ℤ]
    intro i
    refine ⟨b0.repr y i, ?_⟩
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast]
    rfl
  have hinj : Function.Injective ψ := by
    intro y z h
    apply b0.ext_elem
    intro i
    have h2 := congrArg (fun x => ((toG ι).symm x) i) h
    simp only [hψ_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h2
    exact_mod_cast h2
  have hsurj : ∀ x ∈ Submodule.span ℤ (Set.range (gBasis ι)), ∃ y, ψ y = x := by
    intro x hx
    have h := ((gBasis ι).mem_span_iff_repr_mem ℤ x).1 hx
    choose c hc using h
    refine ⟨b0.equivFun.symm c, ?_⟩
    apply (toG ι).symm.injective
    funext i
    rw [hψ_apply]
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show b0.repr (b0.equivFun.symm c) i = c i from by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]]
    have := hc i
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq,
      eq_intCast] at this
    exact this
  let eX : Y ≃ₗ[ℤ] Submodule.span ℤ (Set.range (gBasis ι)) :=
    LinearEquiv.ofBijective (ψ.codRestrict _ hψX)
      ⟨fun y z h => hinj (congrArg Subtype.val h), fun x => by
        obtain ⟨y, hy⟩ := hsurj x x.2
        exact ⟨y, Subtype.ext hy⟩⟩
  have heX : ∀ x, ψ (eX.symm x) = (x : GramSp ι) := fun x =>
    congrArg Subtype.val (eX.apply_symm_apply x)

  have hdY : finrank ℤ Y = Fintype.card ι := finrank_eq_card_basis b0
  have hdV : finrank ℝ (GramSp ι) = Fintype.card ι := finrank_eq_card_basis (gBasis ι)
  have hd : finrank ℤ Y = finrank ℝ (GramSp ι) := hdY.trans hdV.symm
  have hdR : ((finrank ℝ (GramSp ι) : ℕ) : ℝ) = ((finrank ℤ Y : ℕ) : ℝ) := by rw [hd]

  have hvR : LinearIndependent ℝ fun i => ψ (v i) := by
    let e : ι ≃ Fin (finrank ℤ Y) := Fintype.equivFinOfCardEq hdY.symm
    let Mz : Matrix (Fin (finrank ℤ Y)) (Fin (finrank ℤ Y)) ℤ := Matrix.of fun a i => b0.repr (v i) (e.symm a)
    have hMz : Mz.det ≠ 0 := by
      intro h0
      obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      apply hc0
      have hsum : ∑ i, c i • v i = 0 := by
        apply b0.ext_elem
        intro k
        have h1 := congrFun hc (e k)
        simp only [Mz, mulVec, dotProduct, Matrix.of_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1

        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hv c hsum i
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    have hdet : ((Int.castRingHom ℝ).mapMatrix Mz).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, fun h => ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact hi (congrFun h i)
      · funext a
        have h1 := congrArg (fun x => ((toG ι).symm x) (e.symm a)) hg

        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ_apply, map_zero,
        Pi.zero_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h1
        simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Mz,
          eq_intCast, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] at hdet
    exact hMz hdet

  let vX : Fin (finrank ℝ (GramSp ι)) → GramSp ι := fun i => ψ (v (Fin.cast hd.symm i))
  have hvX : LinearIndependent ℝ vX := hvR.comp _ (Fin.cast_injective _)
  obtain ⟨b, hb1, hb2⟩ := ReciprocityTheory.ChartRestriction.G.H1.reducedBasis_holds (GramSp ι)
    (Submodule.span ℤ (Set.range (gBasis ι)))
    ((|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
      (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β) vX hvX
    (fun i => hψX _) (fun i => by rw [hnorm]; exact hvb _)
  refine ⟨(b.map eX.symm).reindex (finCongr hd.symm), fun j => ?_, fun j z => ?_⟩
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hnorm, hbj]
    have h1 := hb1 (Fin.cast hd j)
    rw [hdR] at h1
    calc ‖(b (Fin.cast hd j) : GramSp ι)‖ ^ 2 / 2 ≤ _ := h1
      _ = _ := by ring
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hin, hbj, ← hnorm]
    have h2 := hb2 (Fin.cast hd j) (ψ z) (hψX z)
    rw [hdR] at h2
    exact h2

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

section Col

variable {S : Type} [CommRing S] {n d : ℕ}

def sb (b : Fin n) : Fin 1 × Fin d → MvPowerSeries (Fin n × Fin d) S := fun p => MvPowerSeries.X ((b, p.2))

theorem sb_cc (b : Fin n) (p : Fin 1 × Fin d) : MvPowerSeries.constantCoeff (sb (S := S) b p) = 0 := by
  first
  | simp [sb]

theorem rename_col (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) F = MvPowerSeries.subst (sb b) F := by
  first
  | exact MvPowerSeries.rename_eq_subst _ _
  | (rw [MvPowerSeries.rename_eq_subst]; rfl)
  | (rw [← MvPowerSeries.subst_eq_rename]; rfl)
  | (rw [MvPowerSeries.subst_eq_rename]; rfl)

theorem subst_quadCol (b : Fin n) (r : S) (β : Matrix (Fin d) (Fin d) S) :
    MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) =
      r • ∑ i : Fin d, ∑ j : Fin d, MvPowerSeries.C (β i j) * MvPowerSeries.X (b, i) * MvPowerSeries.X (b, j) := by
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (sb (S := S) (n := n) (d := d) b p) = 0 := fun p => sb_cc b p
  have hs : MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := d) b) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  have hC : ∀ (c : S) (f : MvPowerSeries (Fin 1 × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  have hC' : ∀ (c : S) (f : MvPowerSeries (Fin n × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hs]

  simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Fin.sum_univ_one, mul_assoc, hC, hC', map_smul, map_sum, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs, sb]

theorem sum_subst_quadCol (r : S) (β : Matrix (Fin d) (Fin d) S) :
    ∑ b : Fin n, MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) = r • TB.quadCol (n := n) β := by
  simp only [subst_quadCol]
  simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Finset.smul_sum]

theorem cc_quadCol {m : ℕ} (β : Matrix (Fin d) (Fin d) S) :
    MvPowerSeries.constantCoeff (TB.quadCol (n := m) β) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.TB.quadCol]

end Col

theorem colIdx_degree {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (m : LtN Dw n →₀ ℕ) : (colIdx m).degree = m.degree := by
  classical
  have key : ∀ {α : Type} (e : α →₀ ℕ), e.degree = e.sum (fun _ k => k) := fun e => rfl
  rw [colIdx, key, key, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

private theorem hasSubst_lemma {S σ τ : Type} [CommRing S] [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha

private theorem prod_exp_lemma_2 {S σ ι : Type} [CommRing S] [Algebra ℚ S] (s : Finset ι)
    (x : ι → MvPowerSeries σ S) (hx : ∀ i, MvPowerSeries.constantCoeff (x i) = 0) :
    ∏ i ∈ s, PowerSeries.subst (x i) (PowerSeries.exp S) = PowerSeries.subst (∑ i ∈ s, x i) (PowerSeries.exp S) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  · intro a s ha ih

    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hx a)
    (by rw [map_sum]; exact Finset.sum_eq_zero (fun i _ => hx i))]

theorem harm_kill_jet {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (hj : ∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)))
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (hD : ∀ m ∈ P.support, m.degree ≤ D) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
  classical

  have hccQ : ∀ (r : S) {m' : ℕ}, MvPowerSeries.constantCoeff (r • TB.quadCol (n := m') β) = 0 := by
    intro r m'
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_quadCol, mul_zero]
  have hsb : ∀ b : Fin n, MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := dL Dw) b) :=
    fun b => hasSubst_lemma (sb_cc b)
  have hR : ∀ (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
      MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) F =
        MvPowerSeries.subst (sb b) F := fun b F => rename_col b F

  have hE4 : ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
        ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b) := by
    simp only [hR]
    simp only [MvPowerSeries.subst_mul (hsb _), Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    have hc : ∀ b : Fin n, MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b)
        (PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
        PowerSeries.subst (MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b) ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β))
          (PowerSeries.exp S) := by
      intro b
      have hq : MvPowerSeries.HasSubst (fun _ : Unit => ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β)) :=
        hasSubst_lemma (fun _ => hccQ _)
      exact MvPowerSeries.subst_comp_subst_apply hq (hsb b) (PowerSeries.exp S)
    simp only [hc]
    rw [prod_exp_lemma_2 Finset.univ _ (fun b => ?_), sum_subst_quadCol]
    rw [subst_quadCol]
    simp [MvPowerSeries.smul_eq_C_mul]

  have hE2 : psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g' b)) =
      psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) := by
    refine Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr D (fun b => ?_)
    rw [hR, hR]
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_subst_congr D (sb b) (sb_cc b) (hj b)

  have hK := Formalism.MainNotions.ModuliIntegralCharts.H1.killAddValCol_of ReciprocityTheory.ChartRestriction.G.TB.kernel_additive E H Dw l c S k n
    (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b))
    β (Formalism.MainNotions.ModuliIntegralCharts.H1.psiCover_holds H) hβ a P hP
  have hcan : PowerSeries.subst (-((k : S)) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) = 1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hccQ _) (hccQ _), neg_smul, neg_add_cancel,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.expS, ← mul_assoc, hcan, one_mul] at hK
  calc ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b)
      = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
            ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [← Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g' m, ← hE4]
        congr 1
        unfold Formalism.MainNotions.ModuliIntegralCharts.H1.mVal
        rw [Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet hE2 (by rw [colIdx_degree]; exact hD m hm)]
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m :=
        hK.symm
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) :=
        Finset.sum_congr rfl (fun m _ => by rw [Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g m])

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
end
end

section

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expActOf_of (hE : LinEigSt) : ExpActOfSt := expActOf_of_eig hE

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
