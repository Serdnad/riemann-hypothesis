module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_eigenbasis_fibre : Out.SecTwistSt → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (oa : T.pol.OAct (𝓞 E)) (S : Set (E →+* ℂ)) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), oa.act = T.t.act.act → Function.Bijective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → HasType H T.t.act ρ 1 0 → ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ T.pol.A.left) (τ : Fin x.P.g ≃ S), IsFibreOf T.pol x (gmap K) φ ∧ x.P.g = Module.finrank ℚ E / 2 ∧ IsLieType T.pol oa x φ τ lab := by
  intro hT hL E _ _ _ _ H K _ _ T oa S lab ρ hoa hlab hρ hS hty
  classical
  obtain ⟨-, -, h3⟩ := GlobalTheory.CM.splits_basic E
  obtain ⟨hs1, hs2, -⟩ := h3 K
  have hsp : Splits E K := hs1.2 (by
    rw [← Nat.card_eq_of_bijective lab hlab, Nat.card_eq_fintype_card, NumberField.Embeddings.card])
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨F₀⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  have hg : T.g = Module.finrank ℚ E / 2 := by
    simpa using (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F₀ 1 0 hsp hty hρ).2.2.2.1
  obtain ⟨y, ψ, w, hyg, hψ, hw⟩ := GlobalTheory.KeyPow.exists_keyIn_pullback hT (algebraMap (𝓞 K) K) T.pol (hpos.trans_eq hg.symm)
  have hfib : IsFibreOf T.pol y (spMap (algebraMap (𝓞 K) K)) ψ := ⟨hψ, w, (isGen_iff _).2 hw⟩
  let F : GenFib T.pol := ⟨y.P, ψ, (isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib, y.v, y.basis⟩
  obtain ⟨hrk, hind, -, -, hcard, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F 1 0 hsp hty hρ
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  let res : S → (𝓞 E →+* 𝓞 K) := fun t => RingOfIntegers.mapRingHom (lab t)
  have hres : ∀ t (a : 𝓞 E), ((res t a : 𝓞 K) : K) = lab t (a : E) := fun t a => rfl
  have hinj : Function.Injective res := fun s t h => Subtype.ext (hlab.1
    ((hs2 (res t)).unique (fun a => by rw [← h, hres]) (fun a => by rw [hres])))
  have hrt : ∀ t, res t H.rt = ρ := fun t => RingOfIntegers.ext ((hres t _).trans ((hS t).1 t.2))
  have hcS : Nat.card S = Module.finrank ℚ E / 2 := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective (fun t => ⟨res t, hrt t⟩) ⟨fun s t h => hinj (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨τ', hτ', -⟩ := hs2 τ.1
    obtain ⟨t, rfl⟩ := hlab.2 τ'
    refine ⟨⟨t, (hS t).2 (by rw [hτ', τ.2])⟩, Subtype.ext (RingHom.ext fun a => RingOfIntegers.ext ?_)⟩
    exact (hres _ _).trans (hτ' a)
  have hb : ∀ t : S, ∃ b ∈ Submodule.span K (F.eigLat T.t.act (res t) : Set (Fin F.P₀.g → K)), b ≠ 0 := fun t => by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have := hrk (res t)
    rw [latRank, h, if_pos (hrt t), finrank_bot] at this
    exact zero_ne_one this
  choose b hb hb0 using hb
  have hli : LinearIndependent K b := (hind.comp hinj).linearIndependent _ hb hb0
  have hyg' : y.P.g = Module.finrank ℚ E / 2 := hyg.trans hg
  let e : Fin y.P.g ≃ S := (Finite.equivFinOfCardEq (hcS.trans hyg'.symm)).symm
  let M : Matrix (Fin y.P.g) (Fin y.P.g) K := fun i => b (e i)
  have hM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp e e.injective))
  have := y.P.isAb.comm
  obtain ⟨hex, htan, hcomp, -, hbas⟩ := LieComb.lieComb_algebra K y.P.A _ y.v y.basis.1
  choose v' hv' _ using fun i => hex (M i)
  have hv'b : IsLieBasis v' := (hbas M v' y.basis hv').2 hM
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'b⟩, ψ, e, hfib, hyg', fun a i => ?_⟩
  obtain ⟨-, f₀, -, hf₀, hd⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K T.pol F T.pol F (T.t.act.act a) (T.t.act.hom a)
  have h1 : IsLieComb (r a (M i)) y.v (v' i ≫ f₀) := hd _ (hr a) _ _ (hv' i)
  obtain ⟨w', hw', -⟩ := (LieComb.lieComb_algebra K y.P.A _ v' hv'b.1).1 (Pi.single i (lab (e i) (a : E)))
  have h2 := hcomp _ M v' _ w' hv' hw'
  have h3 : r a (M i) = ∑ j, (Pi.single i (lab (e i) (a : E)) : Fin y.P.g → K) j • M j := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp), Pi.single_eq_same]
    exact ((hr' (res (e i)) _).2.1 (hb (e i)) a).trans rfl
  rw [h3] at h1
  refine ⟨w', hw', ?_⟩
  rw [← (hex _).unique h1 h2, hoa]
  exact (congrArg ((v' i).left ≫ ·) hf₀.symm).trans (Category.assoc _ _ _).symm

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Indep

section Linear

variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype J]

theorem finrank_le_sum {N : J → Submodule K V} (h : ⨆ i, N i = ⊤) :
    Module.finrank K V ≤ ∑ i, Module.finrank K (N i) := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  rw [← Module.finrank_directSum]
  exact LinearMap.finrank_le_finrank_of_surjective hs

theorem iSupIndep_of_sum_le {N : J → Submodule K V} (h : ⨆ i, N i = ⊤)
    (hd : ∑ i, Module.finrank K (N i) ≤ Module.finrank K V) : iSupIndep N := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have he : Module.finrank K (DirectSum J fun i => N i) = Module.finrank K V := by
    rw [Module.finrank_directSum]
    exact le_antisymm hd (finrank_le_sum h)
  exact DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩

theorem sum_finrank_eq {N : J → Submodule K V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank K (N i) = Module.finrank K V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

theorem injective_of_sum_eq {W : J → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] {M : ∀ i, W i →ₗ[K] V} (h : ⨆ i, LinearMap.range (M i) = ⊤)
    (hd : ∑ i, Module.finrank K (W i) = Module.finrank K V) (j : J) : Function.Injective (M j) := by
  have hle : ∀ i ∈ (Finset.univ : Finset J), Module.finrank K (LinearMap.range (M i)) ≤ Module.finrank K (W i) :=
    fun i _ => LinearMap.finrank_range_le _
  have he := (Finset.sum_eq_sum_iff_of_le hle).1
    (le_antisymm (Finset.sum_le_sum hle) (hd ▸ finrank_le_sum h)) j (Finset.mem_univ _)
  have := LinearMap.finrank_range_add_finrank_ker (M j)
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

end Linear


open IntCoord in
theorem map_eigLat_le {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) ≤ F'.eigLat a' τ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem letters_independent : ThetaUnifAV → Out.Laws → IndSt := by
  intro hU hL E _ _ _ H K _ _ ρ σ₁ p q X FA FB M hM N
  classical
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hρ : ρ ≠ 0 := fun h => by
    have := X.ρ_sq
    rw [h] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hsq : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = -ρ ↔ ¬ τ H.rt = ρ := fun τ => by
    have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, X.ρ_sq]; simp
    refine ⟨fun h h' => hρ ?_, fun h => (sq_eq_sq_iff_eq_or_eq_neg.1 e).resolve_left h⟩
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination h - h'
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hA : ∀ b : Bool, (∀ τ : 𝓞 E →+* 𝓞 K, latRank K ((FA b).eigLat (X.A b).t.act τ) =
        if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
      iSupIndep (fun τ : 𝓞 E →+* 𝓞 K =>
        Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K))) ∧
      ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K)) = ⊤ ∧
      (FA b).P₀.g = Module.finrank ℚ E / 2 := by
    rintro (_ | _)
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) (FA false) 0 1 X.split X.typeM X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA false).fib.1]; simpa using d⟩
      rw [a]
      by_cases h : τ H.rt = ρ
      · rw [if_pos h, if_neg (by simpa [hsq] using h)]
      · rw [if_neg h, if_pos (by simpa [hsq] using h)]
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) (FA true) 1 0 X.split X.typeP X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA true).fib.1]; simpa using d⟩
      rw [a]
      simp
  have hB : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := by
    rw [FB.fib.1]
    exact (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ X.B FB p q X.split X.typeB X.ρ_sq).2.2.2.1
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ :=
    GlobalTheory.T.iSup_range_differential_eq_top_of_jointly_onto hU hL K X.B.pol FB σ₁ (Fin p ⊕ Fin q) (fun j => (X.A j.isLeft).pol) (fun j => FA j.isLeft) X.φ M
      inferInstance (fun j => (X.lin j).1) hM fun y => by
        obtain ⟨x, hx⟩ := X.onto y
        exact ⟨p + q, finSumFinEquiv.symm, fun m => x _, hx⟩
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    simp [(hA _).2.2.2, hB, mul_comm]
  have hinj := injective_of_sum_eq hsur hdim
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hrk : ∀ x, latRank K (N x) = latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2) := fun x => by
    rw [latRank, hspan]
    exact (Submodule.equivMapOfInjective _ (hinj x.1) _).finrank_eq.symm
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, ← hsur]
    refine iSup_congr fun j => ?_
    rw [← Submodule.map_top, ← (hA j.isLeft).2.2.1, Submodule.map_iSup]
    exact iSup_congr fun τ => hspan (j, τ)
  refine ⟨fun x => map_eigLat_le (X.lin x.1).2 (hM x.1) x.2, fun x => ?_, hinj, iSupIndep_of_sum_le htop ?_, htop⟩
  · rw [hrk, (hA _).1]
  · rw [← hdim, Fintype.sum_prod_type]
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [← sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1]
    exact Finset.sum_congr rfl fun τ _ => hrk (j, τ)

end GlobalTheory.CM.Indep
end
end
