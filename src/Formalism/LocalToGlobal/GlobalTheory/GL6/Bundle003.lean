module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond
public import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem adelic_GL_ext_local (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ w : HeightOneSpectrum (𝓞 F), bc (prV (E := E) w) g = bc (prV (E := E) w) h) : g = h := by
  ext i j
  have key : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w (g.1 i j - h.1 i j) = 0 := by
    intro w
    have := congrArg (fun x : GL (Fin n) (E ⊗[F] w.adicCompletion F) => x.1 i j) (H w)
    rw [map_sub]; exact sub_eq_zero.2 this
  exact sub_eq_zero.1 (Formalism.UG.P.afsplit_inj _ key)

theorem adelic_comm_disjoint_support (δ δ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v v' : HeightOneSpectrum (𝓞 F))
    (hvv : v ≠ v') (h1 : ∀ w, w ≠ v → bc (prV (E := E) w) δ = 1) (h2 : ∀ w, w ≠ v' → bc (prV (E := E) w) δ' = 1) :
    δ * δ' = δ' * δ := by
  apply adelic_GL_ext_local
  intro w
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw; rw [h2 w hvv, mul_one, one_mul]
  · rw [h1 w hw, mul_one, one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}



theorem diamond_comm_distinct_places (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v v' : (D.mem u).A.vT)
    (hvv : v ≠ v') (a : ((D.mem u).A.Fv v')ˣ) (b : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hdia : ∀ v0 a0 (ψ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) c,
      Formalism.MainNotions.product_first_zeroth_parts.dia D u i v0 a0 ψ c = (D.fm u).dilT i v0 a0 c (ψ ((D.fm u).dil i v0 a0 c)) := fun _ _ _ _ => rfl
  obtain ⟨ka, hka, δa, hδa⟩ := hE i hi v' a
  obtain ⟨kb, hkb, δb, hδb⟩ := hE i hi v b
  have hne : (Tf.atT.eV v).1 ≠ (Tf.atT.eV v').1 := fun h => hvv (Tf.atT.eV.injective (Subtype.ext h))
  have hcomm : δa * δb = δb * δa :=
    Subtype.ext (adelic_comm_disjoint_support δb.1 δa.1 _ _ hne hδb.1 hδa.1).symm
  have hga := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v') hδa hgA
  have hgb := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v) hδb hgA
  funext c
  have e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v' a c) =
      fun z => g ((Tf.cls i hi).y ((D.fm u).dil i v' a c) * δb) ((Tf.val i hi).eY z) := by
    rw [hdia, hval, (Tf.val i hi).dilT v b kb hkb _ δb hδb g hgA]
  have e2 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ ((D.fm u).dil i v b c) =
      fun z => g ((Tf.cls i hi).y ((D.fm u).dil i v b c) * δa) ((Tf.val i hi).eY z) := by
    rw [hdia, hval, (Tf.val i hi).dilT v' a ka hka _ δa hδa g hgA]
  rw [hdia v' a, e1, (Tf.val i hi).dilT v' a ka hka c δa hδa _ hgb,
    hdia v b, e2, (Tf.val i hi).dilT v b kb hkb c δb hδb _ hga]
  funext z
  simp only [mul_assoc, hcomm]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable (D : D7) (u : D.what₂.Word)

theorem emb_tpow_smul (i n : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i (((D.mem u).A.T : D.what₂.LL) ^ n • x) = tpow D u n • (D.fm u).emb i x := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]
  rfl

theorem eval_subP {ι : Type} [Fintype ι] {n : ℕ} (N Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (N x.1 * Z x.1) x.2.1 x.2.2) P =
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => Z x.1 x.2.1 x.2.2) (Formalism.L2.Forms.subP N P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.L2.Forms.subP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, MvPolynomial.eval_X, hp]
    simp [Formalism.L2.Forms.subP, Matrix.mul_apply, MvPolynomial.eval_sum]

theorem fnOf_mul {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (N M : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.fnOf G s (fun τ => N τ * M τ) P =
      Formalism.L2.Forms.fnOf G s M (MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N P) := by
  funext y
  simp only [Formalism.L2.Forms.fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C]
  have h := eval_subP N (fun τ => M τ * y.1 τ) P
  simp only [← Matrix.mul_assoc] at h
  rw [h]
  simp only [Matrix.mul_assoc (N _), Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

def UnramifiedAtLevelPrimes (A : AtTTied u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v (x : 𝓞 D.host.E), A.res v x = 0 →
    (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) ≤
      D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (x : D.host.E)))

theorem not_dvd_prod_of_not_dvd {ι : Type} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, ¬ (D.mem u).A.T ∣ f i) :
    ¬ (D.mem u).A.T ∣ ∏ i ∈ s, f i := by
  have hT : Nat.Prime (D.mem u).A.T := (D.mem u).A.2
  intro hd
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hT.prime f).mp hd
  exact h i hi hdi

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical

variable (D : D7) (u : D.what₂.Word)

def HeckeRationalLevelZero : Prop :=
  ∀ v x, (∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x))

theorem norm_eq_sum_diamond (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    Nm D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, dia D u i v a φ := by
  unfold Nm; rw [LinearMap.sum_apply]

theorem mem_ramified_forms_iff {i : ℕ} (φ : Fn D u i) :
    φ ∈ MramI D u i ↔ φ ∈ (D.fm u).Fi i ∧ ∀ v, Nm D u i v φ = 0 := by
  unfold MramI
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem U_D_of_D_U_on_finite_dim {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (U Dm : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0) (hU : ∀ x ∈ W, U x ∈ W)
    (hDU : ∀ x ∈ W, Dm (U x) = c • x) : ∀ x ∈ W, U (Dm x) = c • x := by
  intro x hx
  have hinj : Function.Injective (U.restrict hU) := by
    intro a b hab
    have h1 : U a = U b := congrArg Subtype.val hab
    have h2 : c • (a : V) = c • (b : V) := by rw [← hDU a a.2, ← hDU b b.2, h1]
    exact Subtype.ext (smul_right_injective V hc h2)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨x, hx⟩
  have hy' : U y = x := congrArg Subtype.val hy
  rw [← hy', hDU y y.2, map_smul]

theorem forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ ((D.fm u).Fi i) := by
  have h := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun a => (D.fm u).emb i (((D.fm u).lat i).b a)))
  rwa [((D.fm u).emb_basis i).2] at h

theorem ramified_forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ (MramI D u i) := by
  have := forms_finite_dimensional D u i
  exact Submodule.finiteDimensional_of_le (inf_le_left : MramI D u i ≤ (D.fm u).Fi i)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Parts

variable (D : D7) (u : D.what₂.Word)

def SeenPlaceLatticeLengthFormula : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))

end Parts

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
