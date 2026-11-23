module

public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.PAdicHodge.Bundle009
public import GroundTheory.PAdicHodge.Bundle007
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.PAdicHodge.UnramifiedClosure
import GroundTheory.LocalFields.Bundle002
public import GroundTheory.PAdicHodge.BCrisEigenFrob
import GroundTheory.PAdicHodge.Bundle008
public import GroundTheory.PAdicHodge.AInfXi
public import GroundTheory.PAdicHodge.FactorizationFactorialLe
public import GroundTheory.PAdicHodge.ACrisFrobFixed
public import GroundTheory.PAdicHodge.Bundle006
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle002
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenChar

open GroundTheory.LocalField EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

theorem algebraMap_padic_cp_injective : Function.Injective (algebraMap ℚ_[p] ℂ_[p]) :=
  (algebraMap ℚ_[p] ℂ_[p]).injective

theorem isometry_algebraMap_padic_cp : Isometry (algebraMap ℚ_[p] ℂ_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' ℂ_[p])

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem eq_of_mul_eq {x : ℂ_[p]} (hx : x ≠ 0) {q q' : ℚ_[p]}
    (h : algebraMap ℚ_[p] ℂ_[p] q * x = algebraMap ℚ_[p] ℂ_[p] q' * x) : q = q' :=
  algebraMap_padic_cp_injective (mul_right_cancel₀ hx h)

theorem exists_eigenChar {x : ℂ_[p]} (hx : x ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) :
    ∃ ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ, Continuous ψ ∧
      ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x := by
  choose q hq using h
  let ψ₀ : Gal(PadicAlgCl p/K) →* ℚ_[p] :=
    { toFun := q
      map_one' := eq_of_mul_eq hx (by rw [← hq, one_smul, map_one, one_mul])
      map_mul' := fun σ τ => eq_of_mul_eq hx (by
        rw [← hq, mul_smul, hq τ, smul_mul', gal_smul_algebraMap, hq σ, map_mul]
        ring) }
  have hcont₀ : Continuous ψ₀ := by
    rw [isometry_algebraMap_padic_cp.isEmbedding.continuous_iff]
    have e : (algebraMap ℚ_[p] ℂ_[p]) ∘ ψ₀ = fun σ => (σ • x) * x⁻¹ := by
      funext σ
      simp only [Function.comp_apply]
      change algebraMap ℚ_[p] ℂ_[p] (q σ) = _
      rw [hq σ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [e]
    exact (continuous_id.smul continuous_const).mul continuous_const
  refine ⟨ψ₀.toHomUnits, ?_, fun σ => hq σ⟩
  rw [Units.continuous_iff]
  refine ⟨hcont₀, ?_⟩
  have e : (fun σ => (((ψ₀.toHomUnits σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) = ψ₀ ∘ fun σ => σ⁻¹ := by
    funext σ
    rw [← map_inv]
    rfl
  rw [e]
  exact hcont₀.comp continuous_inv

theorem norm_eigen_eq_one {x : ℂ_[p]} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)} {q : ℚ_[p]}
    (h : σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) : ‖q‖ = 1 := by
  have h1 := norm_smul_gal σ x
  rw [h, norm_mul, norm_algebraMap'] at h1
  exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx) (h1.trans (one_mul _).symm)

def galRes {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Gal(PadicAlgCl p/L) →* Gal(PadicAlgCl p/K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun k => σ.commutes ⟨(k : PadicAlgCl p), hKL k.2⟩)
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

theorem galRes_apply {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (y : PadicAlgCl p) : galRes hKL σ y = σ y := rfl

theorem exists_fixingSubgroup_of_finite_image (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ) (hψ : Continuous ψ)
    (S : Set Gal(PadicAlgCl p/K)) (hfin : (ψ '' S).Finite) :
    ∃ E : IntermediateField K (PadicAlgCl p), FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, σ ∈ S → ψ σ = 1 := by
  set F := ψ '' S \ {1} with hF
  have hFc : IsClosed F := (hfin.subset Set.sdiff_subset).isClosed
  have hO : ψ ⁻¹' Fᶜ ∈ nhds (1 : Gal(PadicAlgCl p/K)) := by
    refine (hFc.isOpen_compl.preimage hψ).mem_nhds ?_
    simp [hF]
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) _).1 hO
  refine ⟨E, hE, fun σ hσ hS => ?_⟩
  by_contra hne
  exact hsub hσ ⟨⟨σ, hS, rfl⟩, hne⟩

theorem mem_inertia_of_degree {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) :
    ∀ u ∈ unramifiedClosure p, σ u = u := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  have hroot : ∀ ζ ∈ primeToPRoots p, σ ζ = ζ := by
    rintro ζ ⟨m, hm, hcop, hζ⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_iff.2 ⟨m, ?_, hζ⟩))
    intro h0
    rw [CharP.cast_eq_zero_iff _ p] at h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop.symm h0
  intro u hu
  induction hu using IntermediateField.adjoin_induction with
  | mem x hx => exact hroot x hx
  | algebraMap q =>
    exact σ.commutes (algebraMap ℚ_[p] L q)
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_twist_of_unramified {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L] {x : ℂ_[p]} (hx : x ≠ 0) (ψ : Gal(PadicAlgCl p/L) →* ℚ_[p]ˣ)
    (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ c : (AInf ℂ_[p] p)ˣ, ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
      (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  have := isSepClosure_padicAlgCl (L := L)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := L) (Ω := PadicAlgCl p)
    (Multiplicative.ofAdd 1)
  have hw : ‖((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := norm_eigen_eq_one hx (hψx σ₀)
  set w : ℤ_[p]ˣ := PadicInt.mkUnits hw with hwdef
  have hwcoe : ((w : ℤ_[p]) : ℚ_[p]) = ((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p]) := rfl
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (L := L)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := L) w
  set cA := wittToAInf (b : WittVector p (Fpbar p)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[p]) p
  set xc : ℂ_[p] := ((θ cA : normInteger ℂ_[p]) : ℂ_[p]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[p] ℂ_[p] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz0 : ∀ σ, (z σ : ℚ_[p]) ≠ 0 := fun σ h => by
    have := norm_eigen_eq_one hxc (hxcσ σ)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set X := x ^ f * xc⁻¹ with hXdef
  have hX : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero hxc)
  have hXσ : ∀ σ, σ • X = algebraMap ℚ_[p] ℂ_[p]
      (((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹) * X := fun σ => by
    rw [hXdef, ← galCp_apply, map_mul, map_pow, map_inv₀, galCp_apply, galCp_apply, hψx σ, hxcσ σ,
      map_mul, map_pow, map_inv₀]
    have hz' : algebraMap ℚ_[p] ℂ_[p] (z σ : ℚ_[p]) ≠ 0 :=
      (map_ne_zero_iff _ algebraMap_padic_cp_injective).2 (hz0 σ)
    field_simp
    ring
  obtain ⟨ρ, hρc, hρ⟩ := exists_eigenChar hX (fun σ => ⟨_, hXσ σ⟩)
  have hρeq : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) =
      ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹ := fun σ =>
    eq_of_mul_eq hX ((hρ σ).symm.trans (hXσ σ))
  have hz₀ : (z σ₀ : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → (z σ : ℚ_[p]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt p (z σ) * cA = IsPerfectoidField.padicIntToWitt p 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  let ρC : Gal(PadicAlgCl p/L) →* ℂ_[p] :=
    (algebraMap ℚ_[p] ℂ_[p]).toMonoidHom.comp ((Units.coeHom ℚ_[p]).comp ρ)
  have hρC : Continuous ρC :=
    isometry_algebraMap_padic_cp.continuous.comp (Units.continuous_val.comp hρc)
  have hρ1 : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 → ρC σ = 1 := fun σ h => by
    change algebraMap ℚ_[p] ℂ_[p] ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1
    rw [h, map_one]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (hρ1 σ₀ (by rw [hρeq, hz₀, hwcoe, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))]))
    (fun σ hσ => hρ1 σ (by rw [hρeq, hzI σ hσ, hI σ hσ, Units.val_one, one_pow, inv_one, mul_one]))
  refine ⟨f, hf, hcu.unit, fun σ => ⟨z σ, ?_, hz σ⟩⟩
  have h1 : ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 := algebraMap_padic_cp_injective (by
    rw [map_one]
    exact hall σ)
  rw [hρeq] at h1
  exact (mul_inv_eq_one₀ (hz0 σ)).1 h1 |>.symm

end EigenChar

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

section Iteration

variable {A R ι : Type*} [CommRing A] [CommRing R]

theorem exists_eq_add_mul_of_forall {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) (hf : f a = r) (X : R) (ψ : ι → R)
    (h : ∀ y, ∃ b : A, ∃ s : R, ∃ y' : ι, ψ y = f b + X * s + r * ψ y') (y : ι) :
    ∃ b : A, ∃ s : R, ψ y = f b + X * s :=
  _root_.GroundTheory.Variant₂.N1.exists_eq_add_mul_of_forall' f hf X ψ h y

end Iteration

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta 𝒪 p
local notation "φ" => WittVector.frobeniusEquiv p 𝒪♭

theorem exists_p_mul_eq_frobenius_sub {ξ : AInf K p} (hξ : ξ ∈ RingHom.ker θ) :
    ∃ X : ACrisZero K p, (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p := by
  obtain ⟨c, hc⟩ := exists_frobenius_eq ξ
  refine ⟨⟨algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1,
    sub_mem (add_mem (Subalgebra.algebraMap_mem _ c)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem hξ p))) (one_mem _)⟩, ?_⟩
  have h1 := factorial_mul_dpow (K := K) p ξ
  have h2 : algebraMap (AInf K p) 𝔸 (φ ξ) =
      algebraMap (AInf K p) 𝔸 ξ ^ p + (p : 𝔸) * algebraMap (AInf K p) 𝔸 c := by
    rw [hc, map_add (f := _), map_pow, map_mul, map_natCast]
  have h3 : (p : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  show (p : 𝔸) * (algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1) = _
  linear_combination dpow p ξ * h3 + h1 - h2

theorem exists_phiAway_eq_add_mul {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) :
    ∃ b : AInf K p, ∃ s ∈ ACrisZero K p,
      phiAway K p y = algebraMap (AInf K p) 𝔸 b + (X : 𝔸) * s := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [hξ] at hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨w, hw⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (Nat.factorial_ne_zero n)
      (factorization_factorial_le (p := p) n)

    have hd : dpow n (φ ξ) = algebraMap (AInf K p) 𝔸 w * (1 + (X : 𝔸)) ^ n := by
      rw [dpow_eq_iff, ← mul_assoc, ← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, hw,
        map_pow, map_natCast, ← mul_pow, mul_add, mul_one, hX, add_sub_cancel]
    set g := ∑ i ∈ Finset.range n, (1 + (X : 𝔸)) ^ i
    have hg : g ∈ ACrisZero K p :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (add_mem (one_mem _) X.2) i
    have hgeom : (1 + (X : 𝔸)) ^ n = 1 + (X : 𝔸) * g := by
      have := geom_sum_mul (1 + (X : 𝔸)) n
      rw [add_sub_cancel_left] at this
      rw [mul_comm, this]; ring
    refine ⟨w * φ d ^ n, algebraMap (AInf K p) 𝔸 w * g * algebraMap (AInf K p) 𝔸 (φ d) ^ n,
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ w) hg)
        (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) n), ?_⟩
    rw [phiAway_dpow, map_mul, mul_comm (φ d) (φ ξ), dpow_mul, hd, hgeom, map_mul, map_pow]
    ring
  | algebraMap r =>
    exact ⟨φ r, 0, zero_mem _, by rw [phiAway_algebraMap, mul_zero, add_zero]⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    exact ⟨w₁ + w₂, z₁ + z₂, add_mem hz₁ hz₂, by rw [map_add (f := _), e₁, e₂, map_add (f := _)]; ring⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    refine ⟨w₁ * w₂, algebraMap (AInf K p) 𝔸 w₁ * z₂ + z₁ * algebraMap (AInf K p) 𝔸 w₂ +
      (X : 𝔸) * z₁ * z₂, ?_, by rw [map_mul, e₁, e₂, map_mul]; ring⟩
    exact add_mem (add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hz₂)
      (Subalgebra.mul_mem _ hz₁ (Subalgebra.algebraMap_mem _ _)))
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ X.2 hz₁) hz₂)



theorem exists_phi_eq_add_mul [CharZero K] {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p)
    (y : ACris K p) :
    ∃ b : AInf K p, ∃ s : ACris K p, phi (K := K) (p := p) y =
      algebraMap (AInf K p) (ACris K p) b + algebraMap (ACrisZero K p) (ACris K p) X * s := by
  refine exists_eq_add_mul_of_forall (a := (p : AInf K p)) (r := (p : ACris K p))
    (algebraMap (AInf K p) (ACris K p)) (map_natCast _ p) _ (phi (K := K) (p := p)) (fun y => ?_) y
  obtain ⟨y₀, z₁, rfl⟩ := exists_eq_add_p_pow_mul 1 y
  obtain ⟨b, s, hs, e⟩ := exists_phiAway_eq_add_mul hξ hX y₀.2
  refine ⟨b, algebraMap (ACrisZero K p) (ACris K p) ⟨s, hs⟩, z₁, ?_⟩
  have e' : phiZero (K := K) (p := p) y₀ =
      algebraMap (AInf K p) (ACrisZero K p) b + X * ⟨s, hs⟩ :=
    Subtype.ext (by rw [coe_phiZero, e]; rfl)
  have hof : phi (K := K) (p := p) (algebraMap (ACrisZero K p) (ACris K p) y₀) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero (K := K) (p := p) y₀) := phi_of y₀
  have hb : algebraMap (AInf K p) (ACris K p) b =
      algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) b) :=
    AdicCompletion.algebraMap_apply _ b
  rw [RingHom.map_add (phi (K := K) (p := p)), map_mul, pow_one, map_natCast, hof, e',
    RingHom.map_add (algebraMap (ACrisZero K p) (ACris K p)), map_mul, hb]

theorem frobenius_xi_sub_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    φ (AInf.xi ε) - p ∈ Ideal.span {AInf.mu (K := K) ε} := by
  refine AInf.mem_span_mu_of_forall hε hζ fun n => ?_
  rw [map_sub, map_natCast, map_sub, map_natCast, ← RingAut.mul_apply, ← pow_succ,
    AInf.fontaineTheta_frobenius_pow_succ_xi hε n, sub_self]

section Theta

variable [CharZero K]

theorem theta_phi_iterate_algebraMap (n : ℕ) (w : AInf K p) :
    theta (K := K) (p := p) ((phi (K := K) (p := p))^[n] (algebraMap (AInf K p) (ACris K p) w)) =
      θ ((φ ^ n) w) := by
  have h : (phi (K := K) (p := p))^[n] (algebraMap (AInf K p) (ACris K p) w) =
      algebraMap (AInf K p) (ACris K p) ((φ ^ n) w) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, phi_algebraMap, pow_succ', RingAut.mul_apply]
  rw [h, theta_algebraMap]



theorem p_mul_phi_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : ACris K p}
    (hy : ∀ n : ℕ, theta (K := K) (p := p) ((phi (K := K) (p := p))^[n] y) = 0) :
    (p : ACris K p) * phi (K := K) (p := p) y ∈
      Ideal.span {algebraMap (AInf K p) (ACris K p) (AInf.mu ε)} := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi hε hζ
  have hξk : AInf.xi ε ∈ RingHom.ker θ := by rw [hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨X, hX⟩ := exists_p_mul_eq_frobenius_sub hξk
  obtain ⟨b, s, e⟩ := exists_phi_eq_add_mul hξ hX y
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (frobenius_xi_sub_mem_span_mu hε hζ)

  have hXc : (p : ACris K p) * algebraMap (ACrisZero K p) (ACris K p) X =
      algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * algebraMap (AInf K p) (ACris K p) d := by
    have h1 : (p : ACrisZero K p) * X =
        algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε * d) := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, SubringClass.coe_natCast, hX, Subalgebra.coe_algebraMap, mul_comm,
        hd, map_sub, map_natCast]
    have hof : algebraMap (ACrisZero K p) (ACris K p) ((p : ACrisZero K p) * X) =
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) := by
      rw [h1]
      exact (AdicCompletion.algebraMap_apply _ _).symm
    rw [map_mul, map_natCast] at hof
    rw [hof, map_mul]
  have hp0 := AInf.natCast_ne_zero hε hζ

  have e2 : (p : ACris K p) * phi (K := K) (p := p) y =
      algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s := by
    rw [e, mul_add, ← mul_assoc, hXc, map_mul, map_mul, map_natCast]
  have hb : ∀ n : ℕ, θ ((φ ^ n) b) = 0 := by
    intro n
    set Φ := phi (K := K) (p := p) ^ n with hΦ
    have hΦa : ∀ w, theta (K := K) (p := p) (Φ (algebraMap (AInf K p) (ACris K p) w)) =
        θ ((φ ^ n) w) :=
      fun w => by rw [hΦ, RingHom.coe_pow, theta_phi_iterate_algebraMap]
    have h : theta (K := K) (p := p) (Φ (phi (K := K) (p := p) y)) = 0 := by
      rw [hΦ, RingHom.coe_pow, ← Function.iterate_succ_apply]
      exact hy (n + 1)
    have hl : theta (K := K) (p := p) (Φ ((p : ACris K p) * phi (K := K) (p := p) y)) = 0 := by
      rw [map_mul, map_natCast, map_mul, map_natCast, h, mul_zero]
    have hr : theta (K := K) (p := p) (Φ (algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s)) = (p : 𝒪) * θ ((φ ^ n) b) := by
      rw [RingHom.map_add Φ, map_mul Φ, RingHom.map_add (theta (K := K) (p := p)),
        map_mul (theta (K := K) (p := p)), hΦa, hΦa,
        AInf.fontaineTheta_frobenius_pow_mul_mu hε, zero_mul, add_zero, map_mul, map_natCast,
        map_mul, map_natCast]
    rw [e2, hr] at hl
    exact (mul_eq_zero.1 hl).resolve_left hp0
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (AInf.mem_span_mu_of_forall hε hζ hb)
  rw [Ideal.mem_span_singleton']
  refine ⟨(p : ACris K p) * algebraMap (AInf K p) (ACris K p) β +
    algebraMap (AInf K p) (ACris K p) d * s, ?_⟩
  rw [e2, ← hβ]
  simp only [map_mul, map_natCast]
  ring

end Theta

end ACris

end GroundTheory.PAdicHodge
end
