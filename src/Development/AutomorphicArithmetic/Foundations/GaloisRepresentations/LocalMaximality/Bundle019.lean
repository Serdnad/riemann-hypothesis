module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem dual_of_lattice {A F W : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    [AddCommGroup W] [Module F W] [Module A W] [IsScalarTower A F W] (P : Submodule A W)
    [Module.Finite A P] [Module.Projective A P] (hP : Submodule.span F (P : Set W) = ⊤) :
    ∃ (n : ℕ) (v : Fin n → W) (φ : Fin n → W →ₗ[F] F), (∀ k, v k ∈ P) ∧
      (∀ k, ∀ p ∈ P, φ k p ∈ (algebraMap A F).range) ∧ ∀ w, w = ∑ k, φ k w • v k := by
  classical
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let S := nonZeroDivisors A
  have hsurj : ∀ w : W, ∃ (s : S) (p : P), (s : A) • w = (p : W) := by
    intro w
    have hw : w ∈ Submodule.span F (P : Set W) := hP ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem z hz => exact ⟨1, ⟨z, hz⟩, by simp⟩
    | zero => exact ⟨1, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨t, q, h'⟩ := hb
      refine ⟨s * t, (t : A) • p + (s : A) • q, ?_⟩
      simp only [Submonoid.coe_mul, smul_add, Submodule.coe_add, Submodule.coe_smul, ← h, ← h', smul_smul]
      rw [mul_comm (t : A) (s : A)]
    | smul c a _ ha =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S c
      refine ⟨s * t, b • p, ?_⟩
      have ht : algebraMap A F (t : A) * IsLocalization.mk' F b t = algebraMap A F b := IsLocalization.mk'_spec' F b t
      rw [Submodule.coe_smul, ← h, Submonoid.coe_mul, mul_comm, mul_smul, smul_comm (s : A), ← algebraMap_smul F (t : A),
        smul_smul, ht, algebraMap_smul, smul_comm]
  have hloc : IsLocalizedModule S P.subtype := by
    refine ⟨fun s => ?_, fun w => ?_, fun {p q} h => ⟨1, ?_⟩⟩
    · have hs : algebraMap A F (s : A) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b h
        simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul F (s : A) a, ← algebraMap_smul F (s : A) b] at h
        exact smul_right_injective W hs h
      · intro b
        refine ⟨(algebraMap A F (s : A))⁻¹ • b, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul F (s : A), smul_smul, mul_inv_cancel₀ hs, one_smul]
    · obtain ⟨s, p, h⟩ := hsurj w
      exact ⟨(p, s), h⟩
    · have : p = q := Subtype.ext h
      simp [this]
  let ψ : Fin n → P →ₗ[A] F := fun k => Algebra.linearMap A F ∘ₗ LinearMap.proj k ∘ₗ g
  have hunit : ∀ s : S, IsUnit (algebraMap A (Module.End A F) (s : A)) := fun s =>
    IsLocalizedModule.map_units (S := S) (f := Algebra.linearMap A F) s
  let Ψ : Fin n → W →ₗ[A] F := fun k => IsLocalizedModule.lift S P.subtype (ψ k) hunit
  have hΨ : ∀ k (p : P), Ψ k (p : W) = ψ k p := fun k p =>
    IsLocalizedModule.lift_apply S P.subtype (ψ k) hunit p
  let φ : Fin n → W →ₗ[F] F := fun k => (Ψ k).extendScalarsOfIsLocalization S F
  have hφ : ∀ k (p : P), φ k (p : W) = algebraMap A F (g p k) := fun k p => hΨ k p
  have hid : ∀ p : P, (p : W) = ∑ k, φ k (p : W) • ((f (Pi.single k 1) : P) : W) := by
    intro p
    have h1 : f (g p) = p := congrArg (fun u => u p) hfg
    have h2 : g p = ∑ k, g p k • (Pi.single k (1 : A) : Fin n → A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]

    simp [map_sum, hφ, algebraMap_smul]
  refine ⟨n, fun k => (f (Pi.single k 1) : P), φ, fun k => (f (Pi.single k 1)).2, ?_, ?_⟩
  · rintro k p hp
    exact ⟨g ⟨p, hp⟩ k, (hφ k ⟨p, hp⟩).symm⟩
  · have : (LinearMap.id : W →ₗ[F] W) = ∑ k, (φ k).smulRight ((f (Pi.single k 1) : P) : W) := by
      refine LinearMap.ext_on hP ?_
      intro p hp
      simpa using hid ⟨p, hp⟩
    intro w
    simpa using congrArg (fun u => u w) this

private theorem lat_of_isBundle {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (hx : IsPd ℂ x)
    {W V : Type} [AddCommGroup W] [Module F W] [Module ℂ W] [IsScalarTower ℂ F W]
    [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V] (e : W →ₗ[F] V)
    (he : Function.Injective e) (L : Finset (Fin (d + 1)) → Submodule ℂ W) (hL : IsBundle ℂ x L)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (M : Submodule ℂ V)
    (hM : ∀ m ∈ M, ∃ w, e w = m) (hML : ∀ w, w ∈ L I ↔ e w ∈ M) :
    Lat (rA ℂ x I) M ∧ ∀ w, e w ∈ Submodule.span F (M : Set V) := by
  classical
  haveI : IsFractionRing (rA ℂ x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x hx {i} (Finset.singleton_nonempty i)).1
  obtain ⟨s, hs, hsF⟩ := hL.fg i
  let P : Submodule (rA ℂ x {i}) W := Submodule.span (rA ℂ x {i}) (L {i} : Set W)
  have hPs : P = Submodule.span (rA ℂ x {i}) (s : Set W) := by
    change Submodule.span (rA ℂ x {i}) (L {i} : Set W) = _
    rw [hs]
    exact Submodule.span_eq _
  haveI : Module.Finite (rA ℂ x {i}) P := Module.Finite.iff_fg.2 ⟨s, hPs.symm⟩
  haveI : Module.Projective (rA ℂ x {i}) P := hL.proj i
  have hP : Submodule.span F (P : Set W) = ⊤ := by
    rw [eq_top_iff, ← hsF]
    refine Submodule.span_mono fun z hz => ?_
    rw [hPs]
    exact Submodule.subset_span hz
  obtain ⟨n, v, φ, hv, hφ, hid⟩ := dual_of_lattice P hP
  obtain ⟨r, hr⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 he)
  have hre : ∀ w, r (e w) = w := fun w => LinearMap.congr_fun hr w
  have hLI := hL.loc I i hi
  have hLii := hL.loc {i} i (Finset.mem_singleton_self i)
  have hPL : ∀ p ∈ P, p ∈ L {i} := fun p hp => by
    rw [hLii]
    exact hp
  have hLsub : ∀ w ∈ L {i}, w ∈ L I := fun w hw => by
    rw [hLI]
    exact Submodule.subset_span hw
  have hmono : rA ℂ x {i} ≤ rA ℂ x I := Algebra.adjoin_mono fun y ⟨a, ha, h⟩ =>
    ⟨a, by rw [Finset.mem_singleton.1 ha]; exact hi, h⟩
  have hsm : ∀ c ∈ rA ℂ x I, ∀ w ∈ L I, c • w ∈ L I := fun c hc w hw => by
    rw [hLI] at hw ⊢
    exact Submodule.smul_mem (Submodule.span (rA ℂ x I) (L {i} : Set W)) (⟨c, hc⟩ : rA ℂ x I) hw
  have hval : ∀ k, ∀ w ∈ L I, φ k w ∈ rA ℂ x I := by
    intro k w hw
    rw [hLI] at hw
    have hw' : w ∈ Submodule.span (rA ℂ x I) (L {i} : Set W) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy⟩ := hφ k z (Submodule.subset_span hz)
      rw [← hy]
      exact hmono y.2
    | zero => simpa using (rA ℂ x I).zero_mem
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact (rA ℂ x I).add_mem ha hb
    | smul c a _ ha =>
      have : φ k (c • a) = (c : F) * φ k a := by
        rw [show c • a = (c : F) • a from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact (rA ℂ x I).mul_mem c.2 ha
  refine ⟨⟨fun c hc m hm => ?_, n, fun k => e (v k), fun k => φ k ∘ₗ r, fun k => ?_, fun k m hm => ?_, fun m hm => ?_⟩, fun w => ?_⟩
  · obtain ⟨w, rfl⟩ := hM m hm
    rw [← map_smul]
    exact (hML _).1 (hsm c hc w ((hML w).2 hm))
  · exact (hML _).1 (hLsub _ (hPL _ (hv k)))
  · obtain ⟨w, rfl⟩ := hM m hm
    simpa [hre] using hval k w ((hML w).2 hm)
  · obtain ⟨w, rfl⟩ := hM m hm

    simp only [LinearMap.comp_apply, hre, ← map_smul, ← map_sum]
    exact congrArg e (hid w)
  · have hw : w ∈ Submodule.span F (s : Set W) := hsF ▸ Submodule.mem_top
    have hsL : ∀ z ∈ s, e z ∈ M := fun z hz => (hML z).1 (hLsub z (hPL z (by rw [hPs]; exact Submodule.subset_span hz)))
    have hmap : (Submodule.span F (s : Set W)).map e ≤ Submodule.span F (M : Set V) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hsL z hz
    exact hmap ⟨w, hw, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.latOm_of :
    LatOm := by
  intro F K _ _ _ _ _ _ d x hc a I hI
  obtain ⟨i, hi⟩ := hI
  have hB := GlobalTheory.T.regularForms_isBundle_projectiveCover ℂ F K d (xv x) hc a (⋀[K]^a Ω[K⁄ℂ]) (⋀[K]^a Ω[K⁄ℂ]).subtype
    Subtype.val_injective (Submodule.range_subtype _)
  have hle : omB ℂ K (rB ℂ K (xv x) I) a ≤ (⋀[K]^a Ω[K⁄ℂ]).restrictScalars ℂ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, v, -, rfl⟩
    refine (⋀[K]^a Ω[K⁄ℂ]).smul_mem b ?_
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact Submodule.subset_span ⟨_, rfl⟩
  have key := lat_of_isBundle hc.pd (((⋀[K]^a Ω[K⁄ℂ]).subtype).restrictScalars F) Subtype.val_injective _ hB I i hi
    (omB ℂ K (rB ℂ K (xv x) I) a) (fun m hm => ⟨⟨m, hle hm⟩, rfl⟩) (fun w => Iff.rfl)
  exact ⟨key.1, fun w hw => key.2 ⟨w, hw⟩⟩
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Vals
variable {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {e : B →ₐ[ℂ] ℂ}

private lemma val_mul (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨mul_mem p p', map_mul ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_add (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v + v') (c + c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨add_mem p p', map_add ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_zero (hV : ValBasic) : Val B e (0 : L) 0 := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact (hev _ _).2 ⟨zero_mem _, map_zero ev⟩

private lemma val_sum (hV : ValBasic) {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ)
    (h : ∀ i ∈ s, Val B e (f i) (c i)) : Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_zero hV
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact val_add hV (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma val_unique (hV : ValBasic) {v : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v c') :
    c = c' := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  rfl

private lemma val_of_mem (hV : ValBasic) {v : L} (h : v ∈ loc B e) : ∃ c, Val B e v c := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact ⟨_, (hev _ _).2 ⟨h, rfl⟩⟩

end Vals

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma acts_expand (τ : DR ℂ K →ₗ[K] K) {m : ℕ} (w' w : Fin m → DR ℂ K) (v : DR ℂ K) :
    mulP F K (muP F K τ (∑ k, w' k ⊗ₜ w k) v) =
      ∑ k, algebraMap F K (Algebra.trace F K (τ (w' k * v))) • w k := by

  simp only [map_sum, LinearMap.sum_apply, muP_tmul, mulP_tmul]

private lemma omG_ne {d : ℕ} (x : Fin (d + 1) → Fˣ) : algebraMap F K (omG x 0) ≠ 0 := by
  refine (map_ne_zero _).2 ?_
  exact Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.idVal_of :
    LocForms → DtBasic → CRT → TrVal → ResVal → LatA → ValBasic → OmLoc → IdVal := by
  intro hLF hDt hCRT hTV hRV hLat hV hOL F K _ _ _ _ _ _ d x cov τ hτ red a ha m w' w hw hact z
  classical
  obtain ⟨hli, hdt, hvol, -, -⟩ := hDt F K d x cov τ hτ
  set B := rB ℂ K (xv x) ({0} : Finset (Fin (d + 1))) with hB
  set om : K := algebraMap F K (omG x 0) with hom
  have omne : om ≠ 0 := omG_ne x
  have hτv : τ (dtS K x Finset.univ) = om := by
    rw [hvol, map_smul, hτ.1, smul_eq_mul, mul_one]
  have hgEq : ∀ y ∈ omB ℂ K B d, y = (τ y / om) • dtS K x Finset.univ := by
    intro y hy
    have h1 := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K d (xv x) cov).2 τ hτ y (mem_deg_of_mem_omB B d y hy)
    rw [hvol, smul_smul, div_mul_cancel₀ _ omne]
    exact h1
  have hgLoc : ∀ (e : fib ℂ K (xv x)), ∀ y ∈ omB ℂ K B d, τ y / om ∈ loc B e.1 := by
    intro e y hy
    have hle : B ≤ loc B e.1 := (hV K B e.1).1
    have hy' := (hOL K B e.1 d).2.2 _ hle hy
    obtain ⟨c, hc, hce⟩ := (hLF F K d x cov red e d y).1 hy'
    have hp : Finset.univ.powersetCard d = ({Finset.univ} : Finset (Finset (Fin d))) := by
      have := Finset.powersetCard_self (Finset.univ : Finset (Fin d))
      simpa using this
    rw [hp, Finset.sum_singleton] at hce
    have : τ y = c Finset.univ * om := by
      rw [hce, map_smul, hτv, smul_eq_mul]
    rw [this, mul_div_cancel_right₀ _ omne]
    exact hc _
  have hyB : ∀ k (S : Finset (Fin d)), S.card = a → w' k * dtS K x S ∈ omB ℂ K B d := by
    intro k S hS
    have := mul_mem_omB B (d - a) a _ (hw k).1 _ (hS ▸ hdt S)
    rwa [Nat.sub_add_cancel ha] at this
  have hwL : ∀ k, ∃ c : Finset (Fin d) → K, (∀ S, c S ∈ loc B z.1) ∧
      w k = ∑ S ∈ Finset.univ.powersetCard a, c S • dtS K x S := fun k =>
    (hLF F K d x cov red z a (w k)).1 ((hOL K B z.1 a).2.2 _ (hV K B z.1).1 (hw k).2)
  choose b hbl hbe using hwL
  have hφ : ∀ v : K, ∃ c : ℂ, v ∈ loc B z.1 → Val B z.1 v c := by
    intro v
    by_cases hv : v ∈ loc B z.1
    · obtain ⟨c, hc⟩ := val_of_mem hV hv
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose φ hφ using hφ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_laurentConstantTermForm_functionField ℂ F d (xv x) cov.pd
  refine ⟨fun k S => τ (w' k * dtS K x S) / om, b, fun k S => φ (τ (w' k * dtS K x S) / om),
    fun k T => φ (b k T), fun k S hS => hgEq _ (hyB k S hS), hbe, fun k S hS =>
      ⟨hφ _ (hgLoc z _ (hyB k S hS)), hφ _ (hbl k S)⟩, ?_⟩
  intro S T hS hT
  obtain ⟨h, hh⟩ := (hCRT F K d x cov).2 (fun e => if e = z then 1 else 0)
  set g : Fin m → K := fun k => τ (w' k * dtS K x S) / om with hg
  set t : Fin m → F := fun k => Algebra.trace F K (g k * h) with ht
  have hgy : ∀ k, τ (w' k * dtS K x S) = om * g k := by
    intro k
    simp only [hg]
    field_simp
  have htr : ∀ k, Algebra.trace F K (om * (g k * h)) = omG x 0 * t k := by
    intro k
    rw [hom, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have claim1 : ∀ k, t k ∈ rA ℂ (xv x) {0} := by
    intro k
    have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K d (xv x) cov τ hτ {0} ⟨0, by simp⟩ (om * (g k * h))).2
      ⟨(h : K) • (w' k * dtS K x S), smul_mem_omB B d _ h.2 _ (hyB k S hS), by
        rw [map_smul, hgy, smul_eq_mul]; ring⟩ 1 (Subalgebra.one_mem _)
    rw [mul_one, htr] at h1
    have h2 := ((hLat F d x cov.pd {0} 0 (by simp)).2.1 _).1 h1
    have hne : omG x 0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero
    rwa [mul_div_cancel_left₀ _ hne] at h2
  have claim2 : ∀ k, Val B z.1 (algebraMap F K (t k)) (φ (g k)) := by
    intro k
    have hres := hRV F K d x cov ρ hρ z (t k) (claim1 k)
    have hγ0 : ∀ e : fib ℂ K (xv x), ∃ c, Val B e.1 (g k) c := fun e =>
      val_of_mem hV (hgLoc e _ (hyB k S hS))
    choose γ0 hγ0 using hγ0
    have hγ : ∀ e : fib ℂ K (xv x), Val B e.1 (g k * h) (γ0 e * e.1 h) := fun e =>
      val_mul hV (hγ0 e) ((hV K B e.1).2.2.1 h)
    have htv := hTV F K d x cov red ρ hρ (g k * h) (fun e => γ0 e * e.1 h) hγ (claim1 k)
    have hfs : ∑ᶠ e, γ0 e * e.1 h = φ (g k) := by
      rw [finsum_eq_single _ z]
      · rw [hh z]
        simp only [if_true, mul_one]
        exact val_unique hV (hγ0 z) (hφ _ (hgLoc z _ (hyB k S hS)))
      · intro e he
        rw [hh e, if_neg he, mul_zero]
    have : ρ (t k) = φ (g k) := by rw [← hfs]; exact htv
    rwa [this] at hres
  have claim3 : ∑ k, algebraMap F K (t k) • w k = (h : K) • dtS K x S := by
    have h1 := hact ((h : K) • dtS K x S)
      (Submodule.smul_mem _ _ (hS ▸ mem_deg_of_mem_omB B _ _ (hdt S)))
    rw [acts_expand] at h1
    have h2 : ∀ k, algebraMap F K (Algebra.trace F K (τ (w' k * ((h : K) • dtS K x S)))) • w k =
        om • (algebraMap F K (t k) • w k) := by
      intro k
      rw [mul_smul_comm, map_smul, hgy, smul_eq_mul,
        show (h : K) * (om * g k) = om * (g k * h) by ring, htr, map_mul, mul_smul]
    simp only [h2, ← Finset.smul_sum] at h1
    exact smul_right_injective _ omne h1
  have claim4 : ∀ T ∈ Finset.univ.powersetCard a,
      ∑ k, algebraMap F K (t k) * b k T = if S = T then (h : K) else 0 := by
    have hsum : ∑ T ∈ Finset.univ.powersetCard a,
        ((∑ k, algebraMap F K (t k) * b k T) - if S = T then (h : K) else 0) • dtS K x T = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, ← hbe]
      rw [claim3, Finset.sum_ite_eq, if_pos (by simp [Finset.mem_powersetCard, hS]), sub_self]
    intro T hT
    exact sub_eq_zero.1 (linearIndependent_iff'.1 hli _ _ hsum T hT)
  have hTm : T ∈ Finset.univ.powersetCard a := by simp [Finset.mem_powersetCard, hT]
  have hL : Val B z.1 (∑ k, algebraMap F K (t k) * b k T) (∑ k, φ (g k) * φ (b k T)) :=
    val_sum hV _ _ _ fun k _ => val_mul hV (claim2 k) (hφ _ (hbl k T))
  rw [claim4 T hTm] at hL
  have hz1 : Val B z.1 (h : K) 1 := by
    have := (hV K B z.1).2.2.1 h
    rwa [hh z, if_pos rfl] at this
  by_cases hST : S = T
  · rw [if_pos hST] at hL ⊢
    exact val_unique hV hL hz1
  · rw [if_neg hST] at hL ⊢
    exact val_unique hV hL (val_zero hV)
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem kahlerMap_volumeForm {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
    [IsScalarTower ℂ F K'] {d : ℕ} (x : Fin (d + 1) → F) :
    mapDR ℂ K K' (vol0 ℂ K x) = vol0 ℂ K' x := by
  simp only [vol0, ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext j
  have h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w := fun w => by
    simp [mapDR]
  have h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a)) := fun a => by
    simp [map1, ι1, KaehlerDifferential.map_D]
  simp only [Function.comp, h1, map_smul, h2, map_inv₀]
  rw [← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]

theorem UpperTheory.Gal.productCup_of_system.trTop_of :
    TrTop := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ
  haveI : FiniteDimensional F K := hY.covZ.fin
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'
  have hTr := (GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1
  have second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h) := by
    intro h
    rw [← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]
    rw [Algebra.trace_trace]
  refine ⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨⟨τ', hτ'⟩, hvol⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY
  have key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0 := by
    intro i
    have hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧
        (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then
        omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K')) :=
      hy' (Finset.univ.erase i) (Set.mem_univ _)
    by_cases hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty
    · have hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 := by
        simp
      rw [if_pos ⟨hne, hc⟩] at hm
      have hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, -, v, -, rfl⟩
        refine (⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hvol τ' hτ' _ (hle hm), second]
      have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1
        (one_mem _)
      rw [mul_one] at h1
      exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1
    · rw [if_neg (fun h => hne h.1)] at hm
      rw [(Submodule.mem_bot ℂ).1 hm]
      simp
  change trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0

  simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_zsmul, key i, smul_zero]
end
