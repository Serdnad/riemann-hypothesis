module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace PositivityTheory.Rg.BcB.G3.MassP

open GlobalTheory.MassNorm

section

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mass_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.MassTor.mass_eq_of_equiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end

theorem mass_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => mass_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dite_eq_left hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]

end PositivityTheory.Rg.BcB.G3.MassP

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsOntoP

theorem only_rho {k : Type} [Field k] [CharZero k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type}
    [CommRing B] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (hs0 : s ≠ 0) (hcs : c s = -s)
    (x : GL (Fin n) k) (hx : x * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * x)
    (hk : x * δ * thetaGL n c x = δ) : ∃ u, x.val = ρ u := by
  obtain ⟨u, v, huv⟩ := hF.span x.val (by simpa only [Units.val_mul] using congrArg Units.val hx)
  have hA := ClsEqP.A_delta_theta hF hcs x u v huv
  have e : x.val * (δ * thetaGL n c x).val = (ρ u - s • ρ v) * (δ * thetaGL n c x).val := by
    have hk' : x.val * (δ.val * (thetaGL n c x).val) = δ.val := by
      have := congrArg Units.val hk
      simpa only [Units.val_mul, Matrix.mul_assoc] using this
    rw [Units.val_mul, hA, hk']
  have h0 : x.val = ρ u - s • ρ v := by
    have := congrArg (· * ((δ * thetaGL n c x)⁻¹).val) e
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
  have e2 : s • ρ v = -(s • ρ v) := by
    have := huv.symm.trans h0
    rw [sub_eq_add_neg] at this
    exact add_left_cancel this
  have e3 : (2 * s) • ρ v = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [e2]
    exact add_neg_cancel _
  have hv : ρ v = 0 := (smul_eq_zero.mp e3).resolve_left (mul_ne_zero two_ne_zero hs0)
  exact ⟨u, by rw [huv, hv, smul_zero, add_zero]⟩

end PositivityTheory.Rg.BcB.G3.ClsOntoP

namespace PositivityTheory.Rg.BcB.G3

theorem clsOnto_pf : ClsOnto := by
  intro k _ _ n c hc δ s hs0 hcs B _ d ρ hF hsep y hy
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable k n (δ * thetaGL n c δ) (y * thetaGL n c y)
    hy.symm hsep
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) k, y' = h * y * (thetaGL n c h)⁻¹ := ⟨_, rfl⟩
  have hy'N : y' * thetaGL n c y' = δ * thetaGL n c δ := by
    rw [hy']
    simp only [map_mul, map_inv, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc]
    calc h * y * (thetaGL n c h)⁻¹ * (thetaGL n c h * thetaGL n c y * h⁻¹) = h * (y * thetaGL n c y) * h⁻¹ := by
          group
      _ = δ * thetaGL n c δ := by rw [hh]; group
  have hT : thetaGL n c y' * y' = thetaGL n c δ * δ := by
    have := congrArg (thetaGL n c) hy'N
    simpa only [map_mul, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc] using this
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin n) k, a = y' * δ⁻¹ := ⟨_, rfl⟩
  have hcomm : a * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a := by
    calc a * (δ * thetaGL n c δ) = y' * (thetaGL n c δ * δ) * δ⁻¹ := by rw [ha]; group
      _ = y' * (thetaGL n c y' * y') * δ⁻¹ := by rw [hT]
      _ = (y' * thetaGL n c y') * (y' * δ⁻¹) := by group
      _ = (δ * thetaGL n c δ) * a := by rw [hy'N, ha]
  have hkey : a * δ * thetaGL n c a = δ := by
    rw [ha]
    simp only [map_mul, map_inv]
    calc y' * δ⁻¹ * δ * (thetaGL n c y' * (thetaGL n c δ)⁻¹) = (y' * thetaGL n c y') * (thetaGL n c δ)⁻¹ := by
          group
      _ = δ := by rw [hy'N]; group
  have hcomm' : a⁻¹ * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a⁻¹ := by
    calc a⁻¹ * (δ * thetaGL n c δ) = a⁻¹ * ((δ * thetaGL n c δ) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (δ * thetaGL n c δ)) * a⁻¹ := by rw [hcomm]
      _ = (δ * thetaGL n c δ) * a⁻¹ := by group
  have hkey' : a⁻¹ * δ * thetaGL n c a⁻¹ = δ := by
    calc a⁻¹ * δ * thetaGL n c a⁻¹ = a⁻¹ * (a * δ * thetaGL n c a) * thetaGL n c a⁻¹ := by rw [hkey]
      _ = δ := by rw [map_inv]; group
  obtain ⟨u, hu⟩ := ClsOntoP.only_rho hF hs0 hcs a hcomm hkey
  obtain ⟨u', hu'⟩ := ClsOntoP.only_rho hF hs0 hcs a⁻¹ hcomm' hkey'
  have huu : u * u' = 1 := by
    apply hF.inj
    rw [map_mul, ← hu, ← hu', Units.mul_inv, map_one]
  let t : Bˣ := ⟨u, u', huu, by rw [mul_comm, huu]⟩
  have hta : Units.map ρ.toMonoidHom t = a := by
    apply Units.ext
    rw [ClsNormP.units_map_val, hu]
  refine ⟨t, h, ?_⟩
  have hpt : pt δ ρ t = y' := by
    rw [pt, hta, ha]; group
  rw [hpt, hy']
  group

end PositivityTheory.Rg.BcB.G3

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Unit2P

theorem isCompact_fst {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space G]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set G)) := by
  have hc : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_fst
  have hs : (Subgroup.zpowers t.1 : Set G) ⊆ Prod.fst '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

theorem isCompact_snd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set H)) := by
  have hc : IsCompact (Prod.snd '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_snd
  have hs : (Subgroup.zpowers t.2 : Set H) ⊆ Prod.snd '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

end PositivityTheory.Rg.BcB.G3.Unit2P

namespace PositivityTheory.Rg.BcB.G3

theorem unit_pair_of_support (h1 : LocGood) (h2 : GenUnit) (h3 : Supp) : Unit2 := by
  intro E _ _ _ hU a b P₁ hP₁ P₂ hP₂
  filter_upwards [h1 E hU a P₁ hP₁, h1 E hU b P₂ hP₂] with w hw1 hw2
  intro y z hy1 hy2 hz1 hz2 hzK
  obtain ⟨hA1, hB1, hC1⟩ := hw1 z.1 (Subgroup.mem_prod.1 hzK).1 hz1
  obtain ⟨hA2, hB2, hC2⟩ := hw2 z.2 (Subgroup.mem_prod.1 hzK).2 hz2
  set K := (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) with hK
  set θ := (thL a w).prodMap (thL b w) with hθ
  have hnt : ∀ (m : ℕ) (g y : GLw m w),
      (nrmL m w (g⁻¹ * y * thL m w g)).val.charpoly = (nrmL m w y).val.charpoly := by
    intro m g y
    rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hconjK : ∀ y' ∈ K, (nrmL a w y'.1).val.charpoly = atPl w P₁ → (nrmL b w y'.2).val.charpoly = atPl w P₂ →
      ∃ g, y' = g⁻¹ * z * θ g := by
    intro y' hy' e1 e2
    obtain ⟨g1, hg1⟩ := hC1 y'.1 (Subgroup.mem_prod.1 hy').1 e1
    obtain ⟨g2, hg2⟩ := hC2 y'.2 (Subgroup.mem_prod.1 hy').2 e2
    exact ⟨(g1, g2), Prod.ext hg1 hg2⟩
  refine ⟨?_, fun hyK => hconjK y hyK hy1 hy2⟩
  by_cases hex : ∃ g, y = g⁻¹ * z * θ g
  · rw [if_pos hex]
    obtain ⟨g, rfl⟩ := hex
    refine h2 _ θ K z ?_ hzK ?_ ?_ g
    · intro k hk
      exact Subgroup.mem_prod.2 ⟨ThBasic.thL_mem_KGL hU a w _ (Subgroup.mem_prod.1 hk).1,
        ThBasic.thL_mem_KGL hU b w _ (Subgroup.mem_prod.1 hk).2⟩
    · intro g hg
      obtain ⟨t1, ht1, k1, hk1, e1⟩ := hA1 g.1 (Subgroup.mem_prod.1 hg).1
      obtain ⟨t2, ht2, k2, hk2, e2⟩ := hA2 g.2 (Subgroup.mem_prod.1 hg).2
      refine ⟨(t1, t2), ?_, (k1, k2), Subgroup.mem_prod.2 ⟨hk1, hk2⟩, Prod.ext e1 e2⟩
      have ht1' : t1 * z.1 = z.1 * thL a w t1 := ht1
      have ht2' : t2 * z.2 = z.2 * thL b w t2 := ht2
      show (t1, t2) * z = z * θ (t1, t2)
      exact Prod.ext ht1' ht2'
    · intro t ht hc
      have ht' : t * z = z * θ t := ht
      have e1 : t.1 * z.1 = z.1 * thL a w t.1 := congrArg Prod.fst ht'
      have e2 : t.2 * z.2 = z.2 * thL b w t.2 := congrArg Prod.snd ht'
      exact Subgroup.mem_prod.2 ⟨hB1 t.1 e1 (Unit2P.isCompact_fst t hc), hB2 t.2 e2 (Unit2P.isCompact_snd t hc)⟩
  · rw [if_neg hex]
    by_contra hne
    obtain ⟨g, hg⟩ := h3 _ θ K y _ hne
    have hmem : g⁻¹ * y * θ g ∈ K := by
      by_contra hm
      exact hg (Set.indicator_of_notMem (show g⁻¹ * y * θ g ∉ (K : Set (GLw a w × GLw b w)) from hm) _)
    have c1 : (nrmL a w (g⁻¹ * y * θ g).1).val.charpoly = atPl w P₁ := by
      show (nrmL a w (g.1⁻¹ * y.1 * thL a w g.1)).val.charpoly = _
      rw [hnt]; exact hy1
    have c2 : (nrmL b w (g⁻¹ * y * θ g).2).val.charpoly = atPl w P₂ := by
      show (nrmL b w (g.2⁻¹ * y.2 * thL b w g.2)).val.charpoly = _
      rw [hnt]; exact hy2
    obtain ⟨h, hh⟩ := hconjK _ hmem c1 c2
    apply hex
    refine ⟨h * g⁻¹, ?_⟩
    calc y = g * (g⁻¹ * y * θ g) * (θ g)⁻¹ := by group
      _ = g * (h⁻¹ * z * θ h) * (θ g)⁻¹ := by rw [hh]
      _ = (h * g⁻¹)⁻¹ * z * θ (h * g⁻¹) := by rw [map_mul, map_inv]; group

end PositivityTheory.Rg.BcB.G3

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Count2P

theorem rel_equiv {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  constructor
  · exact fun x => ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem mk_eq_iff {G : Type} [Group G] (θ : G →* G) (x z : G) :
    (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x : TwCl θ) = Quot.mk _ z ↔ ∃ g, x = g⁻¹ * z * θ g := by
  constructor
  · intro h
    exact (rel_equiv θ).symm ((rel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h))
  · intro h
    exact (Quot.sound ((rel_equiv θ).symm h))

theorem prod_rel {G H : Type} [Group G] [Group H] (θ₁ : G →* G) (θ₂ : H →* H) (x z : G × H) :
    (∃ g : G × H, x = g⁻¹ * z * (θ₁.prodMap θ₂) g) ↔
      (∃ g₁, x.1 = g₁⁻¹ * z.1 * θ₁ g₁) ∧ (∃ g₂, x.2 = g₂⁻¹ * z.2 * θ₂ g₂) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1, rfl⟩, ⟨g.2, rfl⟩⟩
  · rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩
    exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩

theorem charpoly_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (x z : GLw n w) (h : ∃ g, x = g⁻¹ * z * thL n w g) :
    (nrmL n w x).val.charpoly = (nrmL n w z).val.charpoly := by
  obtain ⟨g, rfl⟩ := h
  have h1 : nrmL n w (g⁻¹ * z * thL n w g) = g⁻¹ * nrmL n w z * g := GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g z
  have h2 : ((g⁻¹ * nrmL n w z * g : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (nrmL n w z : Matrix (Fin n) (Fin n) _) *
        (g : Matrix (Fin n) (Fin n) _) := rfl
  rw [h1, h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g _

end PositivityTheory.Rg.BcB.G3.Count2P

open PositivityTheory.Rg.BcB.G3.Count2P in
theorem PositivityTheory.Rg.BcB.G3.count2_pf (h1 : Count1) : Count2 := by
  intro E _ _ _ hU a b S hS P₁ hP₁ P₂ hP₂ y hy hint
  obtain ⟨zz, hzz, hzK⟩ : ∃ zz : ∀ w : Pl E, GLw a w × GLw b w,
      (∀ w, (Quot.mk _ (zz w) : TwCl ((thL a w).prodMap (thL b w))) = y w) ∧
        ∀ᶠ w in cofinite, zz w ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
    refine ⟨fun w => if h : ∃ z ∈ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))),
        y w = Quot.mk _ z then h.choose else (y w).rep, fun w => ?_, hint.mono fun w hw => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h.choose_spec.2.symm
      · exact Quot.out_eq _
    · dsimp only
      rw [dite_eq_left hw]
      exact hw.choose_spec.1
  have hrel : ∀ w, ∃ g, (y w).rep = g⁻¹ * zz w * ((thL a w).prodMap (thL b w)) g := by
    intro w
    rw [← mk_eq_iff, hzz w]
    exact Quot.out_eq _
  have hc1 : ∀ w, (nrmL a w (zz w).1).val.charpoly = atPl w P₁ := fun w => by
    rw [← (hy w).1]
    exact (charpoly_eq hU a w _ _ ((prod_rel _ _ _ _).1 (hrel w)).1).symm
  have hc2 : ∀ w, (nrmL b w (zz w).2).val.charpoly = atPl w P₂ := fun w => by
    rw [← (hy w).2]
    exact (charpoly_eq hU b w _ _ ((prod_rel _ _ _ _).1 (hrel w)).2).symm
  have e1 : Nat.card {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
      ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} * 2 ^ nfac P₁ =
      2 ^ (a * Fintype.card (InfinitePlace E)) :=
    h1 E hU a S hS P₁ hP₁ (fun w => (zz w).1) hc1 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).1)
  have e2 : Nat.card {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
      ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} * 2 ^ nfac P₂ =
      2 ^ (b * Fintype.card (InfinitePlace E)) :=
    h1 E hU b S hS P₂ hP₂ (fun w => (zz w).2) hc2 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).2)
  have key : ∀ (c : TwCl (thE E a) × TwCl (thE E b)) (w : Pl E),
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w ↔
        (∃ g, locEl a w c.1.rep = g⁻¹ * (zz w).1 * thL a w g) ∧
          (∃ g, locEl b w c.2.rep = g⁻¹ * (zz w).2 * thL b w g) := by
    intro c w
    rw [← hzz w]
    exact (mk_eq_iff _ _ _).trans (prod_rel _ _ _ _)
  let eqv : {c : TwCl (thE E a) × TwCl (thE E b) // ((c.1.rep * thE E a c.1.rep).val.charpoly = P₁ ∧
      (c.2.rep * thE E b c.2.rep).val.charpoly = P₂) ∧ ∀ w ∈ S,
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w} ≃
      {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
        ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} ×
      {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
        ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} :=
    { toFun := fun c => (⟨c.1.1, c.2.1.1, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).1⟩,
        ⟨c.1.2, c.2.1.2, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2.1, p.2.2.1⟩,
        fun w hw => (key (p.1.1, p.2.1) w).2 ⟨p.1.2.2 w hw, p.2.2.2 w hw⟩⟩
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr eqv, Nat.card_prod, add_mul, pow_add, pow_add, ← e1, ← e2]
  ring

end
end
