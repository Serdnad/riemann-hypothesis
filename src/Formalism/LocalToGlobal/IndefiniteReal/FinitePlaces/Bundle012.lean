module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle010
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRhoStable (D : D7) : DRhoStable D := by
  intro ψ θ hψ hθ S T τ z f hf
  exact (Formalism.IndefR.Fock.DRho.thetaDRho D ψ θ hψ hθ (Formalism.IndefR.Eqv.lineAtExists_holds D) S T τ z f hf).1

section Pt

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

lemma theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  convert Formalism.IndefR.Fock.CCR.theta_add_smul hf hg (-1) using 1 <;>
    ext x <;> simp [sub_eq_add_neg]

lemma theta_finsetSum {ι : Type*} (s : Finset ι) (g : ι → WO S T → ℂ) (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ S T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Formalism.IndefR.Fock.CCR.theta_add (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma theta_opPow {ι : Type} (A : ι → (WO S T → ℂ) → (WO S T → ℂ))
    (hA : ∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) (k : ι →₀ ℕ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem ptStable (D : D7) : PtStable D := by
  intro ψ θ hψ hθ S T sS sT BS BT f P hf
  have hA : ∀ (i : FVar D T.rank S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) := by
    intro i g hg
    unfold aPlusAll aPlus crea
    exact Formalism.IndefR.Fock.CCR.theta_smul
      (theta_sub (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg)
        (Formalism.IndefR.Fock.CCR.theta_smul (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg) _)) _
  unfold pureTensorO pureTensorL
  rw [Module.Basis.constr_apply, Finsupp.sum]
  exact theta_finsetSum _ _ fun k _ =>
    Formalism.IndefR.Fock.CCR.theta_smul (theta_opPow _ hA k hf) _

end Pt

end Formalism.IndefR.Fin
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem isSBHalf_iff {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ} :
    IsSBHalf e Λ Φ ↔ Four.IsSB Λ (halfSub S T e) Φ := by
  constructor
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu t => hi u (AddSubgroup.mem_inf.1 hu).1 (AddSubgroup.mem_inf.1 hu).2 t, hl⟩
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu hue t => hi u (AddSubgroup.mem_inf.2 ⟨hu, hue⟩) t, hl⟩

theorem finite_qt_of {H : AddSubgroup (WO S T)} {k : ℕ} (R : Finset (WO S T))
    (hR : ∀ u ∈ H, ∃ r ∈ R, ∃ v ∈ H, u = r + k • v) : Finite (Four.Qt k H) := by
  classical
  let R' : Finset (WO S T) := R.filter (· ∈ H)
  let f : R' → Four.Qt k H := fun r => QuotientAddGroup.mk ⟨r.1, (Finset.mem_filter.1 r.2).2⟩
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H u =>
    obtain ⟨r, hr, v, hv, huv⟩ := hR u u.2
    have hrH : r ∈ H := by
      have := H.sub_mem u.2 (H.nsmul_mem hv k)
      rwa [huv, add_sub_cancel_right] at this
    refine ⟨⟨r, Finset.mem_filter.2 ⟨hr, hrH⟩⟩, ?_⟩
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    refine Four.mem_smulSub.2 ⟨v, hv, ?_⟩
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [huv]
    abel

theorem nsmul_eq_zero_WO {k : ℕ} (hk : 0 < k) {t : WO S T} (h : k • t = 0) : t = 0 := by
  have hu : IsUnit (k : AE D) := by
    have e1 : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := by simp
    rw [e1]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')).map _
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 this

open Classical in
theorem exists_placeModel (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ)
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoX : ∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hvX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u f₀ = f₀)
    (hvY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm ∧
      ∀ Φ, IsSBHalf e₁ Λ Φ → Tm Φ = Four.tfun (heisL ψ S T) (fun t y => ψ (symplO S T t y)) Λ
        (halfSub S T e₁) (halfSub S T (cA D e₁)) f₀ Φ := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨Tm, hTe, htr, hmo, hva⟩ := Four.exists_model (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
    (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁)) (f₀ := f₀)
    (hX := fun x hx x' hx' => heisL_add_half ψ S T he hx hx')
    (hY := fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
    (hXY := fun x _ y _ => heisL_comm ψ S T x y)
    (hχl := fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
    (hχr := fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
    (hχ0 := fun t y => psi_ne_zero ψ _)
    (hLL := fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
    (hdY := fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
    (hfinX := fun k hk => by
      obtain ⟨R, hR⟩ := hfX k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (hfinY := fun k hk => by
      obtain ⟨R, hR⟩ := hfY k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (htf := fun k hk t h => nsmul_eq_zero_WO S T hk h)
    (hoX := fun x hx => hoX x hx) (hoY := fun y hy => hoY y hy)
    (hfX := fun u hu => hvX u (mi hu).1 (mi hu).2)
    (hfY := fun u hu => hvY u (mi hu).1 (mi hu).2)
  refine ⟨Tm, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ hΦ => hTe Φ ((isSBHalf_iff S T).1 hΦ)⟩
  · exact htr Φ ((isSBHalf_iff S T).1 hΦ) x hx
  · exact hmo Φ ((isSBHalf_iff S T).1 hΦ) y hy
  · rw [one_smul]
    exact hva

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def incInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem inf_mul (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * z = incInf D (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    show _ = incInf D (fstA D.host.F a ⊗ₜ[D.host.F] e)
    have : pairA D.host.F 1 0 * a = (fstA D.host.F a, (0 : Af D.host.F)) :=
      Prod.ext (by show (1 : Ainf D.host.F) * a.1 = a.1; rw [one_mul]) (by show (0 : Af D.host.F) * a.2 = 0; rw [zero_mul])
    rw [this]; rfl
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem finite_idempotent_mul_eq (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * z = jF D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, finPart_tmul, jF_tmul]
    congr 1
    exact Prod.ext (by show (0 : Ainf D.host.F) * a.1 = 0; rw [zero_mul]) (by show (1 : Af D.host.F) * a.2 = a.2; rw [one_mul])
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem eq_jF_of_inf (z : AE D) (hz : infPart D z = 0) : z = jF D (finPart D z) := by
  have h1 : pairA D.host.F 1 0 + pairA D.host.F 0 1 = (1 : AF D.host.F) := Prod.ext (add_zero _) (zero_add _)
  calc z = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0 + pairA D.host.F 0 1) * z := by rw [h1, map_one, one_mul]
    _ = jF D (finPart D z) := by rw [map_add (f := _), add_mul, inf_mul, hz, map_zero, zero_add, finite_idempotent_mul_eq]

theorem finPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [jF_tmul, finPart_tmul]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [jF_tmul]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 a ⊗ₜ[D.host.F] e) = 0
    rw [Algebra.TensorProduct.map_tmul]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem approx_Af (a : Af D.host.F) (N : ℕ) (hN : 0 < N) :
    ∃ f : D.host.F, ∃ c ∈ intAf D.host.F, a = algebraMap D.host.F (Af D.host.F) f + algebraMap D.host.F (Af D.host.F) N * c := by
  have hNF : (N : D.host.F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F)
    (algebraMap D.host.F (Af D.host.F) (1 / (N : D.host.F)) * a)
  refine ⟨N * u, _, intAf_of_isInt _ hu, ?_⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_one_div_cancel hNF, map_one, one_mul, ← map_mul]
  ring

theorem isAlg_Z (e : D.host.E) : IsAlgebraic ℤ e :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic e)



theorem approx_AfE (N : ℕ) (hN : 0 < N) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : D.host.E, ∃ y ∈ intAE D, z = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
  | tmul a e =>
    obtain ⟨m, hm0, hmint⟩ := IsAlgebraic.exists_integral_multiple (isAlg_Z e)
    have hmF : ((m : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hm0
    let e' : 𝓞 D.host.E := ⟨m • e, hmint⟩
    have he : e = (1 / (m : D.host.F)) • (e' : D.host.E) := by
      show e = (1 / (m : D.host.F)) • (m • e)
      rw [zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap D.host.F D.host.E), ← map_mul,
        one_div_mul_cancel hmF, map_one, one_mul]
    obtain ⟨f, c, hc, hfc⟩ := approx_Af ((1 / (m : D.host.F)) • a) N hN
    refine ⟨f • (e' : D.host.E), c ⊗ₜ[D.host.F] (e' : D.host.E), AddSubgroup.subset_closure ⟨c, hc, e', rfl⟩, ?_⟩
    have hN' : algebraMap D.host.F (Af D.host.F) (N : D.host.F) * c = N • c := by
      rw [map_natCast, nsmul_eq_mul]
    rw [he, ← TensorProduct.smul_tmul, hfc, TensorProduct.add_tmul, hN', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨w, y1, hy1, rfl⟩ := hx
    obtain ⟨w', y2, hy2, rfl⟩ := hy
    exact ⟨w + w', y1 + y2, add_mem hy1 hy2, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end Formalism.IndefR.Fin

end
end
