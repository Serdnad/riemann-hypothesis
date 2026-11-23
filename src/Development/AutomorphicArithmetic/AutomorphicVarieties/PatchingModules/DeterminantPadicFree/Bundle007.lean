module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SelfdualRamified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle004
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· + ·)
  simpa [Function.comp_def, map_add (f := _)] using this

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· * ·)
  simpa [Function.comp_def, map_mul] using this

private theorem ac_sum {ι : Type} (T : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ac_const (I := I) (Γ := Γ) 0
  | insert a T ha ih => simpa only [Finset.sum_insert ha] using ac_add (hf a) ih

private theorem ac_map (L : R → S) (hL : ∀ (N : ℕ) a b, a - b ∈ I ^ N → L a - L b ∈ J ^ N) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun s => L (f s) := by
  intro N
  have h : IsLocallyConstant fun s => Ideal.Quotient.mk (I ^ N) (f s) := hf N
  show IsLocallyConstant fun s => Ideal.Quotient.mk (J ^ N) (L (f s))
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro x
  filter_upwards [h x] with y hy
  rw [Ideal.Quotient.eq] at hy ⊢
  exact hL N _ _ hy

private theorem ac_hom (L : R →+* S) (t : R) {f : Γ → R}
    (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {L t}) fun s => L (f s) := by
  refine ac_map L (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨L c, by rw [← map_pow, ← map_mul, hc, map_sub]⟩

private theorem ac_eta {g : ℕ} (t : R) {f : Γ → DD R g}
    (hf : AdicCont (Ideal.span {(DD.C t : DD R g)}) f) : AdicCont (Ideal.span {t}) fun s => (f s).eta := by
  refine ac_map (fun x : DD R g => x.eta) (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨c, hc⟩ := h
  refine ⟨c.eta, ?_⟩
  have e : (a - b).eta = a.eta - b.eta := rfl
  rw [← e, ← hc, ← map_pow, show (DD.C (t ^ N) : DD R g) = ⟨t ^ N, 0, 0, 0⟩ from rfl]
  simp

private theorem sum_comp {g : ℕ} {ι : Type} (T : Finset ι) (f : ι → DD R g) :
    (∑ i ∈ T, f i).a = ∑ i ∈ T, (f i).a ∧ (∀ j, (∑ i ∈ T, f i).ep j = ∑ i ∈ T, (f i).ep j) ∧
      (∀ j, (∑ i ∈ T, f i).ep' j = ∑ i ∈ T, (f i).ep' j) ∧ (∑ i ∈ T, f i).eta = ∑ i ∈ T, (f i).eta := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  | insert i T hi ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [Finset.sum_insert hi]
    exact ⟨by rw [← h1]; rfl, fun j => by rw [← h2 j]; rfl, fun j => by rw [← h3 j]; rfl, by rw [← h4]; rfl⟩

private theorem epM_eq {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g) := by
  classical
  have hC : ∀ c : R, (DD.C c : DD R g) = ⟨c, 0, 0, 0⟩ := fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := sum_comp Finset.univ (fun j => DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g))
  apply DD.ext
  · rw [h1]
    change (0 : R) = _
    simp [hC]
  · funext j
    rw [h2 j]
    change Z j a b = _
    simp [hC, Pi.single_apply]
  · funext j
    rw [h3 j]
    change (0 : R) = _
    simp [hC]
  · rw [h4]
    change (0 : R) = _
    simp [hC]

end

theorem UpperTheory.V.Pa.Det.ellClosed :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), z ∈ TwZ k x.A → IsClosed {σ : F.G₀ | ell k x.A σ z = 0} := by
  intro l _ F n x k z hz
  unfold TwZ at hz
  obtain ⟨-, hzc, -, -⟩ := hz
  have hmul : ∀ M N : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => M s i j) →
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => N s i j) →
      ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (M s * N s) i j := by
    intro M N hM hN i j
    simp only [Matrix.mul_apply]
    exact ac_sum _ fun m => ac_mul (hM i m) (hN m j)
  have hρ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => x.ρX (DD x.A k.g) s i j := by
    intro i j
    have h := x.cont i j
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_hom DD.C x.t h
  have hκ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)})
      fun s => DD.epM (fun m => (k.κ m s).map ⇑(algebraMap x.A x.A)) i j := by
    intro i j
    simp only [epM_eq]
    refine ac_sum _ fun m => ac_mul ?_ (ac_const _)
    have hm := k.mem m
    unfold SelZ at hm
    obtain ⟨-, hc, -⟩ := hm
    exact ac_hom DD.C x.t (hc i j)
  have hρ1 : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => k.ρ1 x.A s i j := by
    have := hmul (fun s => 1 + DD.epM fun m => (k.κ m s).map ⇑(algebraMap x.A x.A))
      (fun s => x.ρX (DD x.A k.g) s)
      (fun i j => by simpa only [Matrix.add_apply] using ac_add (ac_const _) (hκ i j)) hρ
    intro i j
    exact this i j
  have hprod := hmul z (fun s => k.ρ1 x.A s) hzc hρ1
  have htr : AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (z s * k.ρ1 x.A s).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact ac_sum _ fun i => hprod i i
  have hf : AdicCont (Ideal.span {x.t}) fun s => ell k x.A s z := ac_eta x.t htr
  have sep : ∀ a : x.A, (∀ N : ℕ, Ideal.Quotient.mk (Ideal.span {x.t} ^ N) a = 0) → a = 0 := by
    intro a ha
    refine PowerSeries.ext fun m => ?_
    have h := ha (m + 1)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [show x.t = PowerSeries.X from rfl] at hc
    rw [← hc, PowerSeries.coeff_mul_X_pow']
    simp
  have hset : {σ : F.G₀ | ell k x.A σ z = 0} =
      ⋂ N : ℕ, {s | Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) = 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h N
      rw [h, map_zero]
    · exact sep _
  rw [hset]
  exact isClosed_iInter fun N =>
    ((show IsLocallyConstant fun s => Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) from hf N).isClopen_fiber 0).isClosed
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem henselian_powerSeries (K : Type) [Field K] : HenselianLocalRing (PowerSeries K) := by
  have hR : HenselianRing (PowerSeries K) (Ideal.span {PowerSeries.X}) := inferInstance
  refine { toIsLocalRing := inferInstance, is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  rw [PowerSeries.maximalIdeal_eq_span_X] at h₁ ⊢
  exact hR.is_henselian f hf a₀ h₁ (h₂.map _)

private theorem coe_generalLinearGroup_map_eq_map {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S)
    (g : GL (Fin m) R) :
    ((GeneralLinearGroup.map f g : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      (g : Matrix (Fin m) (Fin m) R).map f := by
  ext i j
  exact GeneralLinearGroup.map_apply f i j g

private theorem map_transpose_mul_mul_eq {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (X Y Z : Matrix (Fin m) (Fin m) R) :
    (Xᵀ * Y * Z).map φ = (X.map φ)ᵀ * Y.map φ * Z.map φ := by
  simp [Matrix.map_mul, Matrix.transpose_map]

theorem UpperTheory.V.Pa.Det.oneBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {m : ℕ} (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin m) (FractionRing (PowerSeries K))) (H : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → ∃ (Q : GL (Fin m) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin m) (PowerSeries K')), (Q : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) := by
  intro K K' G _ _ _ m j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hj₁ hsq hd hdr hHs hdet hσ hsim
  obtain ⟨Q₀, r₀, hQ₀⟩ := Det.latInt r d hd hdr
  have hQ₀m : ∀ g, (r g).1 * Q₀.1 =
      Q₀.1 * (r₀ g).1.map (algebraMap _ _) := by
    intro g
    have := congr_arg Units.val (hQ₀ g)
    simpa only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map] using this
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K)),
      H₁ = Q₀.1ᵀ * H * Q₀ := ⟨_, rfl⟩
  have hH₁s : H₁ᵀ = H₁ := by
    rw [hH₁, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hHs, Matrix.mul_assoc]
  have hQdet : Q₀.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
  have hH₁det : H₁.det ≠ 0 := by
    rw [hH₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQdet hdet) hQdet
  have hsim₀ : ∀ g, ((r₀ g).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ * H₁ *
      (r₀ (σ g)).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (u g) • H₁ := by
    intro g
    have key := hsim g
    simp only [mat, MonoidHom.comp_apply, Units.coeHom_apply] at key
    rw [hH₁]
    calc _ = (Q₀.1 *
            (r₀ g).1.map (algebraMap _ _))ᵀ * H *
          (Q₀.1 *
            (r₀ (σ g)).1.map (algebraMap _ _)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((r g).1 * Q₀.1)ᵀ * H *
          ((r (σ g)).1 * Q₀.1) := by
          rw [← hQ₀m, ← hQ₀m]
      _ = Q₀.1ᵀ *
          ((r g).1ᵀ * H *
            (r (σ g)).1) * Q₀.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [key, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨P, H', r', hP, hr'⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified (A := PowerSeries K)
    (F := FractionRing (PowerSeries K)) H₁ r₀ σ u (A' := PowerSeries K)
    (F' := FractionRing (PowerSeries K)) j₁ f₁ PowerSeries.X PowerSeries.X PowerSeries.X_irreducible
    hj₁.symm hf₁ (IsFractionRing.injective _ _) hH₁s hH₁det hσ hsim₀
  have h2u : IsUnit (2 : PowerSeries K) := by
    rw [← map_ofNat (PowerSeries.C (R := K)) 2]
    exact (isUnit_iff_ne_zero.2 h2).map _
  have hH's : H'.1ᵀ = H' := by
    have e : (H'.1.map
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ =
        H'.1.map (algebraMap _ _) := by
      rw [← hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.transpose_map, hH₁s, Matrix.mul_assoc]
    refine Matrix.ext fun i j => ?_
    exact IsFractionRing.injective _ (FractionRing (PowerSeries K)) (congr_fun (congr_fun e i) j)
  have hH'det : IsUnit H'.1.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 H'.isUnit
  haveI := henselian_powerSeries K'
  obtain ⟨P₂, hP₂⟩ := UpperTheory.V.AlgebraTools.orthonormal_local j₂ H'.1
    h2u hH's hH'det hsq
  refine ⟨GeneralLinearGroup.map (f₂.comp f₁) Q₀ * GeneralLinearGroup.map f₂ P *
      GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂,
    (MulAut.conj P₂⁻¹).toMonoidHom.comp (pushRep j₂ r'), ?_, ?_⟩
  · have s1 : (Q₀.1.map (f₂.comp f₁))ᵀ *
        H.map (f₂.comp f₁) * Q₀.1.map (f₂.comp f₁) =
        (H₁.map f₁).map f₂ := by
      rw [← map_transpose_mul_mul_eq, ← hH₁, Matrix.map_map]
      rfl
    have s2 : (P.1.map f₂)ᵀ * (H₁.map f₁).map f₂ *
        P.1.map f₂ =
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := by
      rw [← map_transpose_mul_mul_eq, hP, Matrix.map_map, Matrix.map_map]
      congr 1
      funext a
      exact hf₂ a
    have s3 : (P₂.1.map
        (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))))ᵀ *
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) *
        P₂.1.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = 1 := by
      rw [← map_transpose_mul_mul_eq, hP₂, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Units.val_mul, Units.val_mul, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map]
    rw [← s3, ← s2, ← s1]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro g
    have t1 := congr_arg (GeneralLinearGroup.map (f₂.comp f₁)) (hQ₀ g)
    rw [map_mul, map_mul] at t1
    have t2 : GeneralLinearGroup.map (f₂.comp f₁) (GeneralLinearGroup.map (algebraMap (PowerSeries K)
        (FractionRing (PowerSeries K))) (r₀ g)) * GeneralLinearGroup.map f₂ P =
        GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (GeneralLinearGroup.map j₂ (r' g)) := by
      apply Units.ext
      have t2m := congr_arg (fun M => Matrix.map M f₂) (hr' g)
      simp only [Matrix.map_mul, Matrix.map_map] at t2m
      simp only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map, Matrix.map_map]
      have fe1 : (⇑(f₂.comp f₁) ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
          (⇑f₂ ∘ fun a => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (j₁ a)) :=
        funext fun a => by simp [hf₁]
      have fe2 : (⇑(algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ∘ ⇑j₂) =
          (⇑f₂ ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) :=
        funext fun a => by simp [hf₂]
      rw [fe1, fe2]
      exact t2m
    simp only [pushRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      inv_inv] at t1 ⊢
    calc _ = (GeneralLinearGroup.map (f₂.comp f₁) (r g) * GeneralLinearGroup.map (f₂.comp f₁) Q₀) *
          GeneralLinearGroup.map f₂ P *
          GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂ := by
          simp only [mul_assoc]
      _ = _ := by
          rw [t1, mul_assoc (GeneralLinearGroup.map (f₂.comp f₁) Q₀), t2]
          group
end
