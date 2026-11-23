module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle022
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one : ∀ (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ), corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  first | exact @GlobalTheory.LocLanglands.corner_diagT | exact GlobalTheory.LocLanglands.corner_diagT | (intros; apply GlobalTheory.LocLanglands.corner_diagT <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  first | exact @GlobalTheory.CornerUnip.corner_unipB_superDiag | exact GlobalTheory.CornerUnip.corner_unipB_superDiag | (intros; apply GlobalTheory.CornerUnip.corner_unipB_superDiag <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.long_element_conj_involutive : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  first | exact @GlobalTheory.longElt_invT_involution | exact GlobalTheory.longElt_invT_involution | (intros; apply GlobalTheory.longElt_invT_involution <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.long_element_conj_unipotent_borel : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧ superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  first | exact @GlobalTheory.UnipFlip.longElt_invT_conj_unipB | exact GlobalTheory.UnipFlip.longElt_invT_conj_unipB | (intros; apply GlobalTheory.UnipFlip.longElt_invT_conj_unipB <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.long_element_conj_unipotent_radical : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  first | exact @GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | exact GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | (intros; apply GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclE_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) a) =
      inclE (F := F) (v.adicCompletion F) (σ a) := by
  simp [sigR, inclE]

theorem sigR_mem_intV_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] v.adicCompletion F}
    (hs : s ∈ intV E v) : sigR σ (v.adicCompletion F) s ∈ intV E v := by
  have key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v
      rw [sigR_inclE_adic]
      have h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) :=
        (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
      exact Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _
        ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v
      simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

theorem mul_eq_unit_mul_of_triple_product_one {A : Type} [CommRing A] (a b P Q T : A) (h : P * Q * T = 1) :
    a * b = T * ((a * P) * (b * Q)) := by linear_combination (-(a * b)) * h

theorem eq_one_add_mul_neg_of_add_mul_eq_one {A : Type} [CommRing A] (a T S : A) (h : a + T * S = 1) : a = 1 + T * (-S) := by
  linear_combination h

theorem mul_sub_eq_of_triple_product_one {A : Type} [CommRing A] (P Q T d e : A) (h : P * Q * T = 1) (hd : d = 1 + T * e) :
    P * (d * Q - Q) = e := by linear_combination (P * Q) * hd + e * h

end SlopeTestRemainingChoices



theorem uloc_acts_trivially_on_dual_quotient {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (hqp : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T ≠ 0)
    (hLb : S.Lb = rll_dLat n ((p : E)⁻¹))
    (hdual : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hH : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, zero_mul])
  have hq0 : (q : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, mul_zero])
  have hΛ : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hLb]; exact rll_mem_loc_dLat n v _ (inv_ne_zero hp0) z
  have hΛ' : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)) ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) (q : E) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hdual]; exact rll_mem_loc_dLat n v _ hq0 z
  rw [S.UlocAlt v hv] at hx
  obtain ⟨⟨hU, hstL⟩, hstL', hfix⟩ := hx
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hιdef
  set ℓ := lastIdx n with hℓ
  set X := (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) with hX
  have hQQ : ι (q : E) * ι ((q : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have hPQi : ι ((p : E)⁻¹) * ι ((q : E)⁻¹) * (T : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [← map_natCast ι T, ← map_mul, ← map_mul, ← hpq]
    rw [show (p : E)⁻¹ * (q : E)⁻¹ * ((p : E) * (q : E)) = 1 by field_simp, map_one]
  have hPQ : ι (p : E) * ι (q : E) = (T : E ⊗[F] v.adicCompletion F) := by
    rw [← map_mul, hpq, map_natCast]

  set w : Fin n → E ⊗[F] v.adicCompletion F := Pi.single ℓ (ι ((q : E)⁻¹)) with hwdef
  have hw : w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := by
    refine (hΛ' w).2 ⟨fun i hi => ?_, ?_⟩
    · rw [hwdef, Pi.single_eq_of_ne hi]; exact zero_mem _
    · rw [hwdef, Pi.single_eq_same, hQQ]; exact one_mem _

  have hdec : ∀ z ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z ℓ ∧
      z - (r : E ⊗[F] v.adicCompletion F) • w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    intro z hz
    refine ⟨⟨ι (q : E) * z ℓ, ((hΛ' z).1 hz).2⟩, rfl, (hΛ _).2 ⟨fun i hi => ?_, ?_⟩⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact ((hΛ' z).1 hz).1 i hi
    · have h0 : z ℓ - (ι (q : E) * z ℓ) * ι ((q : E)⁻¹) = 0 := by linear_combination (-z ℓ) * hQQ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_same]
      rw [h0, mul_zero]; exact zero_mem _

  set m := S.fT v hv ⟨w, hw⟩ with hmdef
  have hf : ∀ z : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z.1 ℓ ∧ S.fT v hv z = r • m := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr, hu⟩ := hdec z hz
    refine ⟨r, hr, ?_⟩
    have h1 := S.fT_L v hv ((⟨z, hz⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)))) - r • (⟨w, hw⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))))) hu
    rw [map_sub] at h1
    rw [LinearMap.map_smul] at h1
    rw [sub_eq_zero] at h1
    exact h1
  have hm0 : m ≠ 0 := by
    intro h0
    apply S.fT_ne v hv
    refine LinearMap.ext fun z => ?_
    obtain ⟨r, -, hr⟩ := hf z
    rw [hr, h0, LinearMap.zero_apply]
    exact smul_zero r

  have hXw : X *ᵥ w = fun i => X i ℓ * ι ((q : E)⁻¹) := by
    funext i
    show (fun j => X i j) ⬝ᵥ Pi.single ℓ (ι ((q : E)⁻¹)) = _
    rw [dotProduct_single]
  have hxw : X *ᵥ w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := (hstL' w).1 hw
  have hb : ∀ i, i ≠ ℓ → X i ℓ * ι ((q : E)⁻¹) ∈ intV E v := by
    intro i hi
    have h1 := ((hΛ' _).1 hxw).1 i hi
    rw [congrFun hXw i] at h1
    exact h1
  have hXwi : ∀ i, (X *ᵥ w) i = X i ℓ * ι ((q : E)⁻¹) := fun i => congrFun hXw i
  have hd : X ℓ ℓ ∈ intV E v := by
    have h1 := ((hΛ' _).1 hxw).2
    rw [hXwi ℓ, mul_left_comm, hQQ, mul_one] at h1
    exact h1
  have h2 : ((⟨X ℓ ℓ, hd⟩ : intV E v) - 1) • m = 0 := by
    obtain ⟨r, hr, hrm⟩ := hf ⟨X *ᵥ w, hxw⟩
    have hr' : r = ⟨X ℓ ℓ, hd⟩ := by
      apply Subtype.ext
      rw [hr]
      show ι (q : E) * (X *ᵥ w) ℓ = X ℓ ℓ
      rw [hXwi ℓ, mul_left_comm, hQQ, mul_one]
    have hfx := hfix ⟨w, hw⟩
    rw [sub_smul, one_smul, ← hr', ← hrm, sub_eq_zero]
    exact hfx
  have hU' : cT (sigR σ (v.adicCompletion F)) X * X = 1 := by
    have h1 : cT (sigR σ (v.adicCompletion F)) X * (1 : Matrix (Fin n) (Fin n) E).map ι * X =
        (1 : Matrix (Fin n) (Fin n) E).map ι := hU
    rwa [Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_one] at h1
  have hsum : ∑ j, sigR σ (v.adicCompletion F) (X j ℓ) * X j ℓ = 1 := by
    have h1 := congrFun (congrFun hU' ℓ) ℓ
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simpa only [cT, Matrix.transpose_apply, Matrix.map_apply] using h1
  have hs : ∀ a : E, sigR σ (v.adicCompletion F) (ι a) = ι (σ a) := fun a => sigR_inclE_adic σ v a
  have hsq : σ (q : E) = p := by rw [hqp, hσ]
  have hsQi : sigR σ (v.adicCompletion F) (ι ((q : E)⁻¹)) = ι ((p : E)⁻¹) := by rw [hs, map_inv₀, hsq]
  have hc' : -∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))
      ∈ intV E v :=
    neg_mem (sum_mem fun j hj => mul_mem (sigR_mem_intV_adic σ v (hb j (Finset.ne_of_mem_erase hj)))
      (hb j (Finset.ne_of_mem_erase hj)))
  have h3 : sigR σ (v.adicCompletion F) (X ℓ ℓ) * X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) *
      (-∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))) := by
    apply eq_one_add_mul_neg_of_add_mul_eq_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)] at hsum
    rw [Finset.mul_sum]
    convert hsum using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hsQi]
    exact (mul_eq_unit_mul_of_triple_product_one _ _ _ _ _ hPQi).symm
  obtain ⟨e, he⟩ := hH m hm0 ⟨X ℓ ℓ, hd⟩ ⟨_, hc'⟩ h2 h3
  have he' : X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := he
  have hwΛ : X *ᵥ w - w ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    refine (hΛ _).2 ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.sub_apply, hXwi i, hwdef, Pi.single_eq_of_ne hi, sub_zero]
      exact hb i hi
    · rw [Pi.sub_apply, hXwi ℓ, hwdef, Pi.single_eq_same, mul_sub_eq_of_triple_product_one _ _ _ _ _ hPQi he']
      exact e.2
  intro y hy
  obtain ⟨r, -, hu⟩ := hdec y hy
  have hsplit : X *ᵥ y - y = (X *ᵥ (y - (r : E ⊗[F] v.adicCompletion F) • w) - (y - (r : E ⊗[F] v.adicCompletion F) • w)) +
      (r : E ⊗[F] v.adicCompletion F) • (X *ᵥ w - w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [hsplit]
  exact add_mem (sub_mem ((hstL _).1 hu) hu) (Submodule.smul_mem _ r hwΛ)

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.SignatureFactor

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem exists_factor : ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → p + q = M ∧ (∃ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G) ∧ ∀ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G → ∃ B : Matrix (Fin M) (Fin p ⊕ Fin q) ℂ, A * B = 1 ∧ B * A = 1 := by
  intro M p q G h
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e G) * P.val = Formalism.UG.Jpq p q := hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Units.val (P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) with hQ
  have hPQ : P.val * Q = 1 := by
    rw [hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG' : Qᴴ * Formalism.UG.Jpq p q * Q = reindex e e G := by
    rw [← hP']
    calc Qᴴ * (P.valᴴ * (reindex e e G) * P.val) * Q
        = (P.val * Q)ᴴ * (reindex e e G) * (P.val * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  have hdet : G.det ≠ 0 := by
    intro h0
    have h1 : (Formalism.UG.Jpq p q).det = 0 := by
      rw [← hP', Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, h0]; simp
    have h2 := congrArg Matrix.det (Jpq_mul_self p q)
    rw [Matrix.det_mul, h1] at h2
    simp at h2
  refine ⟨?_, ⟨Q.submatrix id e, ?_⟩, ?_⟩
  · simpa using (Fintype.card_congr e).symm
  · ext i j
    have := congrFun (congrFun hG' (e i)) (e j)
    simpa [Matrix.mul_apply] using this
  · intro A hA
    have hBA : (G⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by
      rw [Matrix.mul_assoc, hA]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨_, (Matrix.mul_eq_one_comm_of_equiv e).mp hBA, hBA⟩

end GlobalTheory.Mem.SignatureFactor
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolEmb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infEmb_exists (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E)) :
    ∃ θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  let _ : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : Ainf F →ₐ[F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        change InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) x) w) = _
        rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
        exact DFunLike.congr_fun hw x }
  let g : E →ₐ[F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem infEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ)
    (h' : IsInfEmb τ θ') : θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem existsUnique_infEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : E →+* ℂ, ∃! θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  intro F E _ _ _ _ _ σ h τ
  have := h.1
  have hr : (InfinitePlace.mk (τ.comp (algebraMap F E))).IsReal := IsTotallyReal.isReal _
  have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)
  obtain ⟨θ, hθ⟩ := infEmb_exists τ _ hw
  exact ⟨θ, hθ, fun θ' h' => infEmb_unique τ θ' θ h' hθ⟩

end GlobalTheory.Mem.VolEmb
end
end
