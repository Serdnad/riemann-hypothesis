module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle203
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle368
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Desc.W

section Coeff

variable {T R : Type} [TopologicalSpace T] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private theorem cc_prod {I : Type} (s : Finset I) (f : I → T → R[X]) (h : ∀ i j, Continuous fun t => (f i t).coeff j) :
    ∀ j, Continuous fun t => (∏ i ∈ s, f i t).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j; simpa using continuous_const
  | insert i s hi ih =>
    intro j
    simp only [Finset.prod_insert hi, coeff_mul]
    exact continuous_finsetSum _ fun x _ => (h i _).mul (ih _)

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
private theorem cc_charpoly {a : ℕ} (M : T → Matrix (Fin a) (Fin a) R) (hM : Continuous M) (j : ℕ) :
    Continuous fun t => (M t).charpoly.coeff j := by
  simp only [Matrix.charpoly, Matrix.det_apply, finsetSum_coeff, Polynomial.coeff_smul]
  refine continuous_finsetSum _ fun σ _ => ?_
  have h := cc_prod Finset.univ (fun i t => (M t).charmatrix (σ i) i) (fun i k => by
    simp only [Matrix.charmatrix_apply, coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact hM.matrix_elem _ _
    · exact continuous_const) j
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e
  · simpa [e] using h
  · simpa [e] using continuous_neg.comp' h


end Coeff

private theorem algSat_eq' (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton]

private theorem prod_algSat_sum (n q : ℕ) {I : Type} (s : Finset I) (B : I → Multiset ℂˣ) :
    ((algSat n q (∑ i ∈ s, B i)).map fun b => X - C b).prod = ∏ i ∈ s, ((algSat n q (B i)).map fun b => X - C b).prod := by
  classical
  simp only [algSat_eq']
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a n : ℕ) (s t : ℝ)
    (h : ((a : ℝ) - 1) / 2 + -s = ((n : ℝ) - 1) / 2 + t) (B : Multiset ℂˣ) :
    algSat a (normV w) (B.map (· * qPow w (-s))) = algSat n (normV w) (B.map (· * qPow w t)) := by
  have key : ∀ x : ℝ, ((((normV w : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (qPow w x : ℂ) := fun x => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), coe_qPow, Complex.ofReal_natCast]
  simp only [algSat_eq', Multiset.map_map, key]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply]
  rw [← Units.val_mul, ← Units.val_mul, mul_left_comm, ← qPow_add, h, qPow_add, mul_left_comm]

theorem UpperTheory.V.Z.Desc.W.sumAEOf :
    UpperTheory.V.Z.Desc.W.SumAEOf := by
  intro hTw hG E Ω _ _ _ _ _ _ l _ ι n c a d P m ha hP hm he
  let s : (i : Fin c) → Fin (d i) → ℝ := fun i k => ((ex n (d i) k + a i - 1 : ℤ) : ℝ) / 2
  have hreg : ∀ i k, (CG.mk ((P i).twist (GlobalTheory.HeckeGal.Model.absPow E (s i k)))).IsRegAlg := fun i k => (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have hsC : (s i k : ℂ) = (ex n (d i) k : ℂ) / 2 + ((a i : ℂ) - 1) / 2 := by
      simp only [s]; push_cast; ring
    have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (s i k)
    have h1 := (hm i τ).twist (GlobalTheory.HeckeGal.Model.absPow E (s i k))
    rw [(InfType.expo_of_infType E _).2.1 (s i k) hν τ] at h1
    rw [CG.HasInfChar.infChar_eq (π := CG.mk _) h1]
    refine ⟨(he i k τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he i k τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  choose r hc hr using fun i k => hG E Ω l ι (a i) (ha i) (P i) (hP i) (s i k) (hreg i k)
  refine ⟨fun g => ∏ i, ∏ k, (r i k g⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly, ?_, ?_⟩
  · exact cc_prod _ _ fun i => cc_prod _ _ fun k =>
      cc_charpoly _ (Units.continuous_val.comp ((hc i k).comp continuous_inv))
  · intro w hw S hS A hA σ hσ
    have key : ∀ i k, (r i k σ⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly.map ι.toRingHom =
        ((algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2)))).map fun b => X - C b).prod := by
      intro i k
      rw [hr i k w hw _ (hTw E (a i) (P i) (s i k) w (S i) (hS i)) A hA σ hσ, algSat_shift w (a i) n (s i k)]
      simp only [s, ex]; push_cast; ring
    simp only [Polynomial.map_prod, key, satTot, prod_algSat_sum]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.WeilDeligne UpperTheory.V.Af UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Z.Desc.W

private def conjDec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω) (γ : G F Ω)
    (h : γ • A = B) : ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem conjDec_coe {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω)
    (γ : G F Ω) (h : γ • A = B) (u : ↥(Dec (F := F) B)) :
    ((conjDec A B γ h u : ↥(Dec (F := F) A)) : G F Ω) = γ⁻¹ * u * γ := rfl

private theorem conjDec_surj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω)
    (γ : G F Ω) (h : γ • A = B) : Function.Surjective (conjDec A B γ h) := by
  intro v
  refine ⟨⟨γ * v * γ⁻¹, ?_⟩, ?_⟩
  · have hv := mem_Dec.1 v.2
    have hA : γ⁻¹ • B = A := by rw [← h, inv_smul_smul]
    rw [mem_Dec, mul_smul, mul_smul, hA, hv, h]
  · apply Subtype.ext
    rw [conjDec_coe]
    group

theorem unlOf : UpperTheory.V.Z.Desc.W.UnlOf := by
  intro F Ω _ _ _ _ _ l _ n r w A hA ψ hψ hne A' hA'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  obtain ⟨g, hg⟩ := hψ
  refine ⟨fun i => (ψ i).comp (conjDec A A' γ hγ), ⟨g * r γ⁻¹, fun s => ?_⟩, ?_⟩
  · have key : g * r γ⁻¹ * r s * (g * r γ⁻¹)⁻¹ = g * r (conjDec A A' γ hγ s : G F Ω) * g⁻¹ := by
      rw [conjDec_coe, map_mul, map_mul, map_inv]
      group
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [key]
      simpa using (hg (conjDec A A' γ hγ s)).1 i j hij
    · rw [key]
      simpa using (hg (conjDec A A' γ hγ s)).2 i
  · intro i j hij
    apply hne i j
    ext1 u
    obtain ⟨v, rfl⟩ := conjDec_surj A A' γ hγ u
    have h1 := DFunLike.congr_fun hij v
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [h1, conjDec_coe, map_mul, map_mul, map_inv]
    congr 1
    rw [mul_comm _ ((GlobalTheory.GalOfCusp.cycBar F Ω l) γ), ← mul_assoc, mul_inv_cancel, one_mul]

end UpperTheory.V.Z.Desc.W
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
theorem UpperTheory.V.Z.Desc.W.onePart :
    UpperTheory.V.Z.Desc.W.OnePart := by
  intro hJS hTw E _ _ _ n c hn a d P π had hw
  obtain ⟨s, -⟩ := hJS E (Σ i : Fin c, Fin (d i)) Unit (fun x => a x.1) (fun _ => n)
    (fun x => CG.mk ((P x.1).twist
      (GlobalTheory.HeckeGal.Model.absPow E (-(((x.2 : ℕ) : ℝ) - ((d x.1 : ℝ) - 1) / 2)))))
    (fun _ => CG.mk π) (fun x => (had x.1).1) (fun _ => hn)
    (hw.mono fun w ⟨S, h1, h2⟩ => ⟨_, fun _ => satTot w d S, fun x => hTw E _ _ _ w _ (h1 x.1), fun _ => h2, by
      simp only [neg_neg, Finset.univ_unique, Finset.sum_singleton, satTot]
      exact Fintype.sum_sigma _⟩)
  have hc : ∑ i, d i = 1 := by simpa using Fintype.card_congr s
  have hle : c ≤ ∑ i, d i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (had i).2)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨by omega, fun i => le_antisymm ?_ (had i).2⟩
  rw [← hc]
  exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end

section

theorem UpperTheory.V.Z.Desc.W.satTw :
    UpperTheory.V.Z.Desc.W.SatTw := by
  intro E _ _ _ a P s w B h
  have h1 := (GlobalTheory.CuspRep.CG.HasSat.twist_absPow h s).1
  have h2 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s).2.1 w
  have h3 : GlobalTheory.WeilDeligne.qPow w (-s) = (GlobalTheory.HeckeGal.Model.absPow E s).val w := by
    refine Units.ext ?_
    rw [h2, GlobalTheory.WeilDeligne.coe_qPow]
    simp only [Formalism.ConjugateSelfDual.normV, Complex.ofReal_neg]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h3]
  exact h1
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem comm_one {G H : Type} [Group G] [CommGroup H] (f : G →* H) (s t : G) : f ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement]
  exact (Commute.all _ _).commutator_eq

private theorem lpDim_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).lpDim = x.lpDim := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.lpDim_mk, WD.lpDim_mk]

private theorem gd_lpTwist {x : WD h} (hx : Gd x) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : Gd (x.lpTwist ξ hξ) := by
  refine ⟨fun s t => ?_, (GlobalTheory.GalCut7.IwahoriTwist.monodromy_vanishes_weilTwist_iff x ξ hξ).2 hx.2⟩
  have h1 : WD.charPol x ⁅s, t⁆ = _ := hx.1 s t
  show WD.charPol _ _ = _
  rw [GlobalTheory.GalCut.SsTwist.charPol_lpTwist, comm_one ξ s t, lpDim_lpTwist, h1]
  simp

end WD

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem good_chars {n : ℕ} {x : IrrGL (k := k)} (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hs : HasSupport x.rep (GlobalTheory.RoadU.chars ξ hξ)) : Good x := by
  refine ⟨_, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
  simp [IrrGL.ofChar]

private theorem good_zero (τ : SmIrr (GL (Fin 0) k)) : Good (IrrGL.of τ.ρ τ.smooth τ.irred) := by
  have hex : ∃ (t : ℕ) (x : Fin t → IrrGL (k := k)) (hx : ∑ a, (x a).1 = 0)
      (φ : τ.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr x hx)),
      (∀ a, (x a).IsCusp) ∧ Function.Injective φ ∧
        HasSupport τ.ρ (Finset.univ.val.map x) := by
    obtain ⟨t, x, hx, hc, φ, hφ⟩ :=
      GlobalTheory.CompanionTheory.SubEmb.subEmbedding_of_stage GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 0 _ τ.ρ τ.smooth τ.irred
    have hsupp : HasSupport τ.ρ (Finset.univ.val.map x) :=
      GlobalTheory.LocGL.hasSupport_of_isSubquotient τ.irred hc (.of_injective φ hφ)
    exact ⟨t, x, hx, φ, hc, hφ, hsupp⟩
  obtain ⟨t, x, hx, -, hc, -, hs⟩ := hex
  refine ⟨_, hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred), fun y hy => ?_⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  have h0 := (Finset.sum_eq_zero_iff.1 hx) a (Finset.mem_univ a)
  have h1 := (hc a).1
  omega

end Loc

end UpperTheory.V.Z.Desc.W
end
end
