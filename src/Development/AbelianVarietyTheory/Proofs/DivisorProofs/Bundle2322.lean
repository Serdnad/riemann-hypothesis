module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplitting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

theorem exists_finset_cosets {A : Type} [Group A] (U₀ U : Subgroup A) (h : U.relIndex U₀ ≠ 0) :
    ∃ F : Finset A, ∀ u ∈ U₀, ∃ f ∈ F, f ∈ U₀ ∧ ∃ v ∈ U, u = f * v := by
  haveI : (U.subgroupOf U₀).FiniteIndex := ⟨h⟩
  haveI : Finite (U₀ ⧸ U.subgroupOf U₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (U₀ ⧸ U.subgroupOf U₀)
  refine ⟨Finset.univ.image (fun q : U₀ ⧸ U.subgroupOf U₀ => ((q.out : U₀) : A)), ?_⟩
  intro u hu
  set q : U₀ ⧸ U.subgroupOf U₀ := QuotientGroup.mk ⟨u, hu⟩
  refine ⟨((q.out : U₀) : A), Finset.mem_image_of_mem _ (Finset.mem_univ _), (q.out).2,
    ((q.out : U₀) : A)⁻¹ * u, ?_, by group⟩
  have h1 : (q.out)⁻¹ * ⟨u, hu⟩ ∈ U.subgroupOf U₀ := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GlobalTheory.CentCls

namespace GlobalTheory.CentCls

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  intro p hp G L K' hK' β x t hx hsh y₀ _ _ r
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨F₂, hF₂⟩ := exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hK'.1.relIndex_ne_zero
  let ι : G.GAf →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
    { toFun := fun g => g, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let U₁ : Subgroup ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    ((L.K.toSubgroup.map (MulAut.conj r₁).toMonoidHom).map ι).comap (psiAway G x)
  let U₂ : Subgroup ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :=
    ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj r₂).toMonoidHom).comap (psiP G)
  obtain ⟨O₁, hO₁, h1O₁, hO₁K⟩ :=
    exists_open_psiAway_mem_conj_level p G L β x t hx (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) r₁
  obtain ⟨O₂, hO₂, h1O₂, hO₂K⟩ := GlobalTheory.T.psi_p_neighborhood_in_level_subgroup p G r₂
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel G.C G.star (β : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) p
    (U₁.prod U₂) ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩,
      fun z hz hT1 _ => Subgroup.mem_prod.mpr ⟨by
        obtain ⟨k, hk, hk'⟩ := hO₁K z.1 hz.1 hT1
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_map.mpr ⟨r₁ * k * r₁⁻¹, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hk'⟩), by
        have h2 := hO₂K z.2 hz.2
        refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨r₂⁻¹ * psiP G z.2 * r₂, h2, ?_⟩)
        show r₂ * (r₂⁻¹ * psiP G z.2 * r₂) * r₂⁻¹ = psiP G z.2
        group⟩⟩
  let Pf : G.Cˣ × ℚˣ → Prop := fun e =>
    (e.1 : G.C) * β * MulOpposite.unop (G.star e.1) = algebraMap ℚ G.C e.2 * β ∧
      Commute (e.1 : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
  let e₀ : G.Cˣ × ℚˣ := if h : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 then h.choose else 1
  let S' := S ∪ S.image (fun s => dg G.C p e₀ * s)
  let gOf : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ → G.GAf := fun w =>
    if h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w then h.choose else 1
  have hgOf : ∀ w (g : G.GAf), (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w →
      ((gOf w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := by
    intro w g hg
    have h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := ⟨g, hg⟩
    simp only [gOf, dif_pos h]
    exact h.choose_spec
  refine ⟨(S' ×ˢ F₂).image (fun q => (gOf (psiAway G x q.1.1) * r₁, psiP G q.1.2 * r₂ * q.2)), ?_⟩
  intro c hc
  obtain ⟨c₁, c₂⟩ := c
  have hc1 : c₁ * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c₁ := congrArg Prod.fst hc
  have hc2 : c₂ * toP1 G β y₀ = toP1 G β y₀ * c₂ := congrArg Prod.snd hc
  have hz₁ := inT_psiAway_inv_of_commute p G β x t hx y₀ c₁ hc1
  obtain ⟨z₂, hz₂, hz₂c⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G β hsh y₀ c₂ hc2
  obtain ⟨γ, hγf, hγc, s, hs, u, hu, hz⟩ := hS (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) hz₁ hz₂
  obtain ⟨γ', ⟨hγ'f, hγ'c⟩, hγ'pos, s', hs', hds⟩ : ∃ γ' : G.Cˣ × ℚˣ, Pf γ' ∧ (0 : ℚ) < (γ'.2 : ℚ) ∧
      ∃ s' ∈ S', dg G.C p γ * s = dg G.C p γ' * s' := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hex : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 := ⟨γ, ⟨hγf, hγc⟩, hneg⟩
      have he₀ : e₀ = hex.choose := by simp only [e₀, dif_pos hex]
      obtain ⟨⟨he1, he2⟩, he3⟩ := hex.choose_spec
      refine ⟨γ * e₀⁻¹, ⟨?_, ?_⟩, ?_, dg G.C p e₀ * s,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      · rw [he₀]
        exact form_mul_inv G.star (β : G.C) γ.1 hex.choose.1 γ.2 hex.choose.2 hγf he1
      · rw [he₀]
        show Commute ((γ.1 * hex.choose.1⁻¹ : G.Cˣ) : G.C) _
        rw [Units.val_mul]
        exact hγc.mul_left he2.units_inv_left
      · rw [he₀]
        show (0 : ℚ) < ((γ.2 * hex.choose.2⁻¹ : ℚˣ) : ℚ)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr he3)
      · rw [map_mul, map_inv]
        group
    · exact ⟨γ, ⟨hγf, hγc⟩, hpos, s, Finset.mem_union_left _ hs, rfl⟩
  let y : grp G β := ⟨γ', hγ'f, hγ'pos⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
  obtain ⟨g, hg1, hg⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu1)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨k₂, hk₂, hk₂e⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu2)
  obtain ⟨f, hf, -, v, hv, hkv⟩ := hF₂ k₂ hk₂
  have hz' : (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) = dg G.C p γ' * s' * u := by
    rw [hz, hds]
  have hz1 := congrArg Prod.fst hz'
  have hz2 := congrArg Prod.snd hz'
  simp only [Prod.fst_mul, Prod.snd_mul] at hz1 hz2
  have hc₁ : (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    simp [psiAway_apply, mul_assoc]
  have e1 : psiAway G x (dg G.C p γ').1 = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    (toAfF_eq_psiAway G β x t hx y).symm
  rw [hz1, map_mul, map_mul, e1, ← hg] at hc₁
  have hs1 : ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x s'.1 := by
    refine hgOf _ ((toAfF G β x t hx y)⁻¹ * c₁ * g⁻¹) ?_
    show ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)⁻¹ *
      (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * (ι g)⁻¹ = _
    rw [hc₁]
    group
  have hc₁' : c₁ = toAfF G β x t hx y * gOf (psiAway G x s'.1) * g := by
    apply Subtype.ext
    show (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) *
      ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * ι g
    rw [hs1]
    exact hc₁
  have e2 : psiP G (dg G.C p γ').2 = toP1 G β y := (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G β y).symm
  have hc₂' : c₂ = toP1 G β y * psiP G s'.2 * (r₂ * k₂ * r₂⁻¹) := by
    rw [← hz₂c, hz2, map_mul, map_mul, e2, ← hk₂e]
    rfl
  have hg' : g = r₁ * k * r₁⁻¹ := hkg.symm
  have hmem : (s', f) ∈ S' ×ˢ F₂ := Finset.mem_product.mpr ⟨hs', hf⟩
  refine ⟨y, Subtype.ext (Prod.ext (Units.ext hγ'c.eq) (mul_comm _ _)), _,
    Finset.mem_image_of_mem _ hmem, (k, v), hk, hv, ?_⟩
  rw [hc₁', hg', hc₂', hkv]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

end GlobalTheory.CentCls
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealMove

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem frMove_mul {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (hX : IsMod W rfl X)
    (u v : GA D W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * v) x = frMove θ W rfl X u (frMove θ W rfl X v x) := by
  funext τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have e : realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1 =
      realM θ (Formalism.L2.Theta.mt W u) τ.1 * realM θ (Formalism.L2.Theta.mt W v) τ.1 := by
    unfold realM
    rw [dite_eq_left hτ, dite_eq_left hτ, dite_eq_left hτ, GlobalTheory.UnitaryChar.compAt_mt_mul]
  show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) =
    Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) *
      (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W v) τ.1) * mat x τ)
  rw [e, ← Matrix.mul_assoc]
  simp

theorem om_real_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x hx f φ hf hR
  subst hr
  have hstd := hP.weil.std
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hP.inf hP.even hP.std hX hS
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hP.inf, X', m, g, X.p0, hq', bas', idx', hs, hP.even⟩ with hC
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨hIsB, hinv, -, -, -, -, -, hmv, hTh⟩ := hBx B hB
  have hfe : f = C.Th (C.xB B) φ := (hTh f φ hR.1).1 ⟨hf, hR⟩
  have hON : ∀ u, IsONFr X (frMove θ W rfl X u x) := fun u => (hmv u).1
  have hpres : ∀ u : GA D W, IsThetaFunO ψ V W (om (1, u) f) := fun u => hP.weil.om_pres _ _ hf
  have hc : ∀ u : GA D W, ∃ c : ℂ, u ∈ GinfC W → ‖c‖ = 1 ∧
      Reads θ V W rfl X bas idx (om (1, u) f) (c • φ) (frMove θ W rfl X u x) := by
    intro u
    by_cases hu : u ∈ GinfC W
    swap
    · exact ⟨1, fun h => absurd h hu⟩
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D V W C om (GlobalTheory.Ker.isWeak_of_datum hP.weil) 1 (one_mem _)
      u hu B hIsB
    refine ⟨c, fun _ => ⟨hc1, ?_⟩⟩
    have h1 := hc φ hR.1
    rw [← hfe] at h1
    obtain ⟨-, -, -, -, -, -, -, -, hTh'⟩ := (hfr _ (hON u)).2 _ (hmv u).2
    have h2 := ((hTh' (C.Th (C.xB (C.mvB u B)) φ) φ hR.1).2 rfl).2
    have h3 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON u)
      _ _ _ _ h2 h2).1 c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at h3
    rw [h1]
    exact h3
  choose c hc using hc
  by_cases hφ : φ = 0
  · intro u hu
    have := (hc u hu).2
    rw [hφ, smul_zero] at this ⊢
    exact this
  obtain ⟨G, hG⟩ := GlobalTheory.T.inner_thetaFunctions_reading_testFunction_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
  obtain ⟨K, hK0, hK⟩ := (hG x x hx hx).2.2 φ hR.1 hφ
  obtain ⟨μ, 𝓕, hμ⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D V W C).1
  have hmul : ∀ u ∈ GinfC W, ∀ v ∈ GinfC W, c (u * v) = c u * c v := by
    intro u hu v hv
    have h1 := hK _ _ (hON (u * v)) (hON u) _ _ _ _ (hpres _) (hpres _) (hc _ (mul_mem hu hv)).2 (hc u hu).2 μ 𝓕 hμ
    have hR1 : Reads θ V W rfl X bas idx f ((1 : ℂ) • φ) x := by rwa [one_smul]
    have h2 := hK _ _ (hON v) hx _ _ _ _ (hpres _) hf (hc v hv).2 hR1 μ 𝓕 hμ
    have h3 := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hP.weil μ 𝓕 hμ (1, u) _ _ (hpres v) hf
    have h4 : om (1, u * v) f = om (1, u) (om (1, v) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [h4, h3, h2, frMove_mul θ W X hX, (hG _ _ (hON v) hx).2.1 u, map_one, mul_one] at h1
    have h5 : c v = c (u * v) * conj (c u) :=
      mul_right_cancel₀ (mul_ne_zero hK0 (hG _ _ (hON v) hx).1) h1
    have h6 : c u * conj (c u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (hc u hu).1]; simp
    rw [h5]
    linear_combination (-c (u * v)) * h6
  have hmu0 : ∀ u, mu u ≠ 0 := fun u h => by
    have := hmu.norm u
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _
    hx hinv).1
  have hone := GlobalTheory.UnitaryChar.char_eq_one D θ W hP.inf _ hcart (fun u => c u / mu u)
    (fun u hu v hv => by
      show c (u * v) / mu (u * v) = c u / mu u * (c v / mu v)
      rw [hmul u hu v hv, muVal_mul hmu, mul_div_mul_comm])
    (fun k hk hks => by
      have h1 := GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x _ hx hinv f φ hf hR k hk hks
      have h2 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON k)
        _ _ _ _ (hc k hk).2 h1).2.1 rfl
      have h3 : c k = mu k := smul_left_injective ℂ hφ h2
      show c k / mu k = 1
      rw [h3, div_self (hmu0 k)])
  intro u hu
  have h : c u = mu u := (div_eq_one_iff_eq (hmu0 u)).1 (hone u hu)
  rw [← h]
  exact (hc u hu).2

end GlobalTheory.RealMove
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem semiLat_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ →
    ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C))
      (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))),
      SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ H
  have key : ∀ {P : Subgroup (GAd σ J)}, P ≤ fixG σ J C →
      (ratPts σ J ⊓ fixG σ J C).subgroupOf P = (ratPts σ J).subgroupOf P := fun h => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩
  obtain ⟨hC, -, cM, cN, hN, hP, hd, hn, -⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ H
  haveI := locallyCompact_unipRad H.cm H.herm hC
  obtain ⟨ν, DN, hν, hDN, h1⟩ := exists_mass_one (cocompact_unipRad H.cm H.herm hC)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := cM.locallyCompactSpace
  have hDM := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom
    ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) Measure.haar
  refine ⟨ν, Measure.haar, DN, _,
    { closedN := cN
      closedM := cM
      norm := fun x hx u hu => (hn x (hP hx.1) u).1 hu
      disj := hd
      dec := ?_
      haarN := hν
      haarM := inferInstance
      domN := by rw [key hN]; exact hDN
      domM := by rw [key inf_le_left]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J j m C D Z J₀ H _ _ inferInstance hDM }⟩
  rintro γ ⟨hγ, hf⟩
  obtain ⟨u, hu, x, hx, e, hr⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ H γ hf
  refine ⟨u, hu, x, hx, ⟨?_, hN hu⟩, ⟨hr hγ, hx.1⟩, e⟩
  have : u = γ * x⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.SphEis
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.linear_model_double_splitting : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  first | exact @GlobalTheory.DblLin.dblLin | exact GlobalTheory.DblLin.dblLin | (intros; apply GlobalTheory.DblLin.dblLin <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.linear_bar_local_theta_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  first | exact @GlobalTheory.OppLinOp.local_op_eq_smul | exact GlobalTheory.OppLinOp.local_op_eq_smul | (intros; apply GlobalTheory.OppLinOp.local_op_eq_smul <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_weil_functional_translation_equivariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) →
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  first | exact @GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero | exact GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero | (intros; apply GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_weil_functional_spherical_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  first | exact @GlobalTheory.SchurCharV.exists_char_of_schur | exact GlobalTheory.SchurCharV.exists_char_of_schur | (intros; apply GlobalTheory.SchurCharV.exists_char_of_schur <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.local_unitary_action_schwartz_inf : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ' : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ' w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ≠ v → φ' w = φ w) ∧ Acts (evFin F v) (om' (g, h)) (φ v) (φ' v) ∧ om' (g, h) (pure f φ) = pure f φ' := by
  first | exact @GlobalTheory.PureStabOne.pure_stab_one | exact GlobalTheory.PureStabOne.pure_stab_one | (intros; apply GlobalTheory.PureStabOne.pure_stab_one <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_bar_functional_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι → ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  first | exact @GlobalTheory.WeilTransferW.unitaryW_acts_right | exact GlobalTheory.WeilTransferW.unitaryW_acts_right | (intros; apply GlobalTheory.WeilTransferW.unitaryW_acts_right <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_weil_functional_good_place_equivariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  first | exact @GlobalTheory.ShapeUV.shapeV | exact GlobalTheory.ShapeUV.shapeV | (intros; apply GlobalTheory.ShapeUV.shapeV <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_weil_functional_local_uniqueness : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  first | exact @GlobalTheory.MixedForm.char_eq_local | exact GlobalTheory.MixedForm.char_eq_local | (intros; apply GlobalTheory.MixedForm.char_eq_local <;> assumption)
end
