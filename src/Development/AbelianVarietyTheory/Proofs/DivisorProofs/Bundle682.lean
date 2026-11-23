module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.FinLevSim

def mulSub (O L : Type) [Ring O] [AddCommGroup L] [Module O L] (N : ℕ) : Submodule O L where
  carrier := {x | ∃ y, x = N • y}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (smul_add N a b).symm⟩
  zero_mem' := ⟨0, (smul_zero N).symm⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, smul_comm c N a⟩

theorem finite_quot (O L : Type) [Ring O] [AddCommGroup L] [Module O L] [Module.Finite ℤ L] {N : ℕ}
    (hN : 0 < N) : Finite (L ⧸ mulSub O L N) := by
  have h1 : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
  have h2 : AddGroup.FG (L ⧸ mulSub O L N) :=
    AddGroup.fg_of_surjective (f := (mulSub O L N).mkQ.toAddMonoidHom) (mulSub O L N).mkQ_surjective
  refine AddCommGroup.finite_of_fg_torsion _ ?_
  intro x
  obtain ⟨x, rfl⟩ := (mulSub O L N).mkQ_surjective x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨N, hN, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

theorem mem_of_dvd {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℕ) (x : D.La)
    (h : ∀ y, ((p ^ r : ℕ) : ℤ) ∣ D.EF x y) : ∃ y, x = (p ^ r) • y := by
  obtain ⟨e, he, hperf⟩ := D.perfP
  have hN : ((p ^ r : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos r).ne'
  choose q hq using h
  let f₀ : D.La →ₗ[ℤ] ℤ :=
    { toFun := q
      map_add' := fun a b => mul_left_cancel₀ hN (by rw [mul_add, ← hq, ← hq, ← hq, map_add (f := _)])
      map_smul' := fun c a => mul_left_cancel₀ hN (by
        rw [← hq, map_smul, hq]; simp only [smul_eq_mul, RingHom.id_apply]; ring) }
  obtain ⟨w, hw⟩ := hperf f₀
  have h1 : e • x = (p ^ r) • w := by
    apply D.nondeg
    ext y
    rw [map_nsmul, map_nsmul, hw]
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hq]
    show (e : ℤ) * (((p ^ r : ℕ) : ℤ) * q y) = ((p ^ r : ℕ) : ℤ) * ((e : ℤ) * q y)
    ring
  have hc : IsCoprime (e : ℤ) ((p ^ r : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (he.pow_right r)
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a • w + b • x, ?_⟩
  have h2 : (e : ℤ) • x = ((p ^ r : ℕ) : ℤ) • w := by rw [natCast_zsmul, natCast_zsmul, h1]
  calc x = (a * (e : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • x := by rw [hab, one_smul]
    _ = (p ^ r) • (a • w + b • x) := by
      rw [add_smul, mul_smul, h2, ← natCast_zsmul, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a,
        mul_comm b]

theorem exists_level_pairing_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (r : ℕ) (W : Q → Q → kˣ) (ζ : kˣ), IsPrimitiveRoot ζ (p ^ r) → (∀ a a' b : Q, a ^ (p ^ r) = 1 → a' ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (a * a') b = W a b * W a' b) → (∀ a b : Q, a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W a b * W b a = 1) → (∀ (c : D.O) (a b : Q), a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (act c a) b = W a (act (D.star c).unop b)) → (∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W a b = 1) → a = 1) → ∀ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) → ∃ f' : D.La → Q, ((∀ x y, f' (x + y) = f' x * f' y) ∧ (∀ (c : D.O) x, f' (c • x) = act c (f' x)) ∧ (∀ x, f' x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f' x = g)) ∧ ∀ x y, W (f' x) (f' y) = ζ ^ D.EF x y := by
  intro p _ D k _ _ _ Q _ act r W ζ hζ Wadd Wskew Wadj Wnd f ⟨fadd, flin, fker, fonto⟩
  have hN : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  haveI := D.finLa
  set K := mulSub D.O D.La (p ^ r) with hK
  haveI : Finite (D.La ⧸ K) := finite_quot D.O D.La hN
  have surj : Function.Surjective K.mkQ := K.mkQ_surjective
  let s : D.La ⧸ K → D.La := Function.surjInv surj
  have hs : ∀ x, K.mkQ (s x) = x := Function.surjInv_eq surj
  have hs' : ∀ x, ∃ y, s (K.mkQ x) = x + (p ^ r) • y := by
    intro x
    have : s (K.mkQ x) - x ∈ K := (Submodule.Quotient.eq K).1 (hs (K.mkQ x))
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [← hy]; abel⟩
  have hmk : ∀ x, K.mkQ x = 0 ↔ ∃ y, x = (p ^ r) • y := fun x => Submodule.Quotient.mk_eq_zero K
  let fb : D.La ⧸ K → Q := fun x => f (s x)
  have hfb : ∀ x, fb (K.mkQ x) = f x := by
    intro x
    obtain ⟨y, hy⟩ := hs' x
    show f (s (K.mkQ x)) = f x
    rw [hy, fadd, (fker _).2 ⟨y, rfl⟩, _root_.mul_one]
  have fbadd : ∀ x y, fb (x + y) = fb x * fb y := by
    intro x y
    obtain ⟨x, rfl⟩ := surj x
    obtain ⟨y, rfl⟩ := surj y
    rw [← map_add (f := _), hfb, hfb, hfb, fadd]
  have fblin : ∀ (c : D.O) x, fb (c • x) = act c (fb x) := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hfb, hfb, flin]
  have fbker : ∀ x, fb x = 1 ↔ x = 0 := by
    intro x
    obtain ⟨x, rfl⟩ := surj x
    rw [hfb, fker, hmk]
  have fbonto : ∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, fb x = g := by
    intro g
    rw [fonto]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, hfb x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  have fbtor : ∀ x, fb x ^ (p ^ r) = 1 := fun x => (fbonto _).2 ⟨x, rfl⟩
  let E : D.La ⧸ K → D.La ⧸ K → kˣ := fun x y => ζ ^ D.EF (s x) (s y)
  have hζ1 : ∀ z : ℤ, ζ ^ (((p ^ r : ℕ) : ℤ) * z) = 1 := fun z =>
    (hζ.zpow_eq_one_iff_dvd _).2 (dvd_mul_right _ _)
  have hE : ∀ x y, E (K.mkQ x) (K.mkQ y) = ζ ^ D.EF x y := by
    intro x y
    obtain ⟨a, ha⟩ := hs' x
    obtain ⟨b, hb⟩ := hs' y
    show ζ ^ D.EF (s (K.mkQ x)) (s (K.mkQ y)) = _
    have : D.EF (x + (p ^ r) • a) (y + (p ^ r) • b) =
        D.EF x y + ((p ^ r : ℕ) : ℤ) * (D.EF x b + D.EF a (y + (p ^ r) • b)) := by
      rw [map_add D.EF, map_nsmul D.EF, LinearMap.add_apply, LinearMap.smul_apply, map_add (D.EF x),
        map_nsmul (D.EF x), nsmul_eq_mul, nsmul_eq_mul]
      ring
    rw [ha, hb, this, zpow_add, hζ1, _root_.mul_one]
  obtain ⟨ε, u, v, hε1, hε2⟩ := GlobalTheory.T.exists_conj_idempotent_mod_prime_pow p D r
  have hkill : ∀ (c : 𝓞 D.F) (x : D.La ⧸ K), algebraMap (𝓞 D.F) D.O ((p : 𝓞 D.F) ^ r * c) • x = 0 := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hmk]
    refine ⟨algebraMap (𝓞 D.F) D.O c • x, ?_⟩
    rw [map_mul, mul_smul, map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hst : (D.star (algebraMap (𝓞 D.F) D.O ε)).unop = algebraMap (𝓞 D.F) D.O (D.bar ε) := by
    rw [D.star_F, MulOpposite.unop_op]
  have hskew : ∀ x y, D.EF x y + D.EF y x = 0 := by
    intro x y
    have h := D.alt (x + y)
    rw [map_add D.EF, LinearMap.add_apply, map_add (f := _), map_add (f := _), D.alt, D.alt] at h
    linarith
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_of_adjoint_skewPairings D.O (fun c => (D.star c).unop) (D.La ⧸ K) k
    (fun x y => W (fb x) (fb y)) E (algebraMap (𝓞 D.F) D.O ε) D.star_star
    (fun c => Algebra.commutes ε c)
    (fun c => by simp only [hst]; exact Algebra.commutes _ c)
    (fun x => by
      simp only [hst]
      rw [← add_smul, ← map_add (f := _), hε1, map_add (f := _), map_one, add_smul, one_smul, hkill, add_zero])
    (fun x => by
      simp only [hst]
      rw [← mul_smul, ← map_mul, hε2, hkill])
    (fun x x' y => by
      simp only [fbadd]
      exact Wadd _ _ _ (fbtor _) (fbtor _) (fbtor _))
    (fun x y => Wskew _ _ (fbtor _) (fbtor _))
    (fun c x y => by
      simp only [fblin]
      exact Wadj _ _ _ (fbtor _) (fbtor _))
    (fun x hx => by
      refine (fbker x).1 (Wnd _ (fbtor _) fun b hb => ?_)
      obtain ⟨y, rfl⟩ := (fbonto b).1 hb
      exact hx y)
    (fun x x' y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨x', rfl⟩ := surj x'
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_add (f := _), hE, hE, hE, map_add (f := _), LinearMap.add_apply, zpow_add])
    (fun x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [hE, hE, ← zpow_add, hskew, zpow_zero])
    (fun c x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_smul, ← map_smul, hE, hE, D.adj])
    (fun x hx => by
      obtain ⟨x, rfl⟩ := surj x
      refine (hmk x).2 (mem_of_dvd D r x fun y => ?_)
      have := hx (K.mkQ y)
      rw [hE] at this
      exact (hζ.zpow_eq_one_iff_dvd _).1 this)
  refine ⟨fun x => fb (g (K.mkQ x)), ⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun q => ?_⟩, fun x y => ?_⟩
  · simp only [map_add (f := _), fbadd]
  · simp only [map_smul, fblin]
  · simp only []
    rw [fbker, g.map_eq_zero_iff, hmk]
  · rw [fbonto]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := surj (g.symm x)
      exact ⟨y, by simp only []; rw [hy, g.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · exact (hg _ _).trans (hE x y)

end GlobalTheory.UPel.HT.FinLevSim
end
end

section

open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj det_ne_zero_of_pos colMat exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

theorem coords_sum {d : ℕ} (π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ)) (S : Matrix (Fin g) (Fin g) ℂ) (k : Fin d) :
    π S k = ∑ i, ∑ j, S i j * π (Matrix.single i j 1) k := by
  conv_lhs => rw [matrix_eq_sum_single S]

  simp only [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (S i j) = S i j • Matrix.single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Pi.smul_apply, smul_eq_mul]

theorem perCoord_exists : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  intro O _ bar g ρ D
  classical
  refine ⟨Module.finrank ℂ (Tsp bar ρ), fun P₀ hP₀ => ?_⟩
  set d := Module.finrank ℂ (Tsp bar ρ)
  let bV := Module.finBasis ℂ (Tsp bar ρ)
  obtain ⟨p, hp⟩ := (Tsp bar ρ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let ι : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := (Tsp bar ρ).subtype ∘ₗ bV.equivFun.symm.toLinearMap
  let π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ) := bV.equivFun.toLinearMap ∘ₗ p
  have hιeq : ∀ b, ι b = ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) := fun b => rfl
  have hιT : ∀ b, ι b ∈ Tsp bar ρ := fun b => by rw [hιeq]; exact Submodule.coe_mem _
  have hpv : ∀ v : Tsp bar ρ, p ((Tsp bar ρ).subtype v) = v := fun v => LinearMap.congr_fun hp v
  have hπι : ∀ b, π (ι b) = b := fun b => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) = (Tsp bar ρ).subtype (bV.equivFun.symm b) from rfl, hpv, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ S ∈ Tsp bar ρ, ι (π S) = S := fun S hS => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show S = (Tsp bar ρ).subtype ⟨S, hS⟩ from rfl, hpv, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨α, β, hαβ⟩ := exists_colMat_per hP₀
  obtain ⟨M₀, hM₀h, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hdet₀ : M₀.det ≠ 0 := det_ne_zero_of_pos hpos₀
  have hu₀ : IsUnit M₀.det := isUnit_iff_ne_zero.2 hdet₀
  have hA₀ : colMat α P₀ = 1 ∧ colMat β P₀ = 0 :=
    realMap_inj (ext_per hP₀ fun x => by rw [← hαβ P₀ hP₀]; simp [realMap_apply])
  let Cf : (D.La → Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun f => (colMat α f)⁻¹ * colMat β f
  let Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ) := fun P => π ((Cf P)ᵀ * M₀)
  let Cof : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (ι b * M₀⁻¹)ᵀ
  let Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)) := fun b => (realMap 1 (Cof b)).toAddMonoidHom.comp P₀
  have hQ : ∀ b x, Q b x = realMap 1 (Cof b) (P₀ x) := fun b x => rfl
  have hCofT : ∀ b, (Cof b)ᵀ * M₀ = ι b := fun b => by
    simp only [Cof, transpose_transpose, nonsing_inv_mul_cancel_right _ _ hu₀]
  obtain ⟨U, hUg, hUo, hU0⟩ := mem_nhds_iff.1 (GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix M₀ hpos₀)
  have hQper : ∀ b, Cof b ∈ U → IsPeriod D ρ (Q b) := fun b hb => by
    obtain ⟨hY, hX, hpos⟩ := hUg hb
    have hT : (Cof b)ᵀ * M₀ ∈ Tsp bar ρ := by rw [hCofT]; exact hιT b
    obtain ⟨hMh, hMim⟩ := GlobalTheory.T.riemann_relation_converse_conjAffine M₀ (Cof b) hM₀h hdet₀ hT.1 hY
    refine GlobalTheory.T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (Cof b)) _ hP₀ (realMap_one_injective hX) (fun a x => ?_) hMh hpos (fun x y => ?_)
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, star_mulVec_map, mulVec_mulVec,
        ← comm_of_mem_Tsp hP₀ hM₀ hdet₀ hT a, ← mulVec_mulVec, mulVec_add]
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, hMim, hM₀]
  have hCofc : Continuous Cof := by
    exact (Continuous.matrix_mul ι.continuous_of_finiteDimensional continuous_const).matrix_transpose
  have hCof0 : Cof 0 = 0 := by simp [Cof, ι]
  have hZ0 : Z P₀ = 0 := by simp [Z, Cf, hA₀]
  have hcol : ∀ γ : Fin g → (D.La →₀ ℂ), Continuous fun f : D.La → Fin g → ℂ => colMat γ f := fun γ =>
    continuous_matrix fun i j => by simp only [colMat, of_apply]; fun_prop
  have hCfc : ContinuousAt Cf ⇑P₀ := by
    refine ContinuousAt.mul ?_ (hcol β).continuousAt
    refine ContinuousAt.comp (f := fun f => colMat α f) ?_ (hcol α).continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [hA₀.1, det_one]
    exact (Ring.inverse_eq_inv' (G₀ := ℂ)) ▸ continuousAt_inv₀ one_ne_zero
  have hCf0 : Cf P₀ = 0 := by simp [Cf, hA₀]
  have hdetc : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := (hcol α).matrix_det
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hdetc.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀.1]) |>.and
      (hCfc.preimage_mem_nhds (hUo.mem_nhds (by rw [hCf0]; exact hU0))))
  refine ⟨Cof ⁻¹' U, Q, Z, s, ε, hUo.preimage hCofc, hε, ⟨fun b hb => hQper b hb, fun x => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let F : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => Cof b *ᵥ star (P₀ x)
        map_add' := fun b b' => by simp only [Cof, map_add (f := _), Matrix.add_mul, transpose_add, add_mulVec]
        map_smul' := fun c b => by
          simp only [Cof, map_smul, Matrix.smul_mul, transpose_smul, smul_mulVec, RingHom.id_apply] }
    have hF : Differentiable ℂ (fun b => F b) := (LinearMap.toContinuousLinearMap F).differentiable
    refine ((differentiableOn_const (P₀ x)).add hF.differentiableOn).congr fun b _ => ?_
    rw [hQ, realMap_apply, one_mulVec]; rfl
  · show Cof (Z P₀) ∈ U
    rw [hZ0, hCof0]; exact hU0
  · ext x
    rw [hZ0, hQ, hCof0, realMap_apply, one_mulVec, zero_mulVec, add_zero]
  · intro b hb _
    have h1 := hαβ (Q b) (hQper b hb)
    have key : colMat α (Q b) = 1 ∧ colMat β (Q b) = Cof b :=
      realMap_inj (ext_per hP₀ fun x => by rw [← h1 x, hQ])
    show π (((colMat α (Q b))⁻¹ * colMat β (Q b))ᵀ * M₀) = b
    rw [key.1, key.2, inv_one, Matrix.one_mul, hCofT, hπι]
  · intro P hP hn
    obtain ⟨hdetA, hCU⟩ := hs _ hn
    have hu : IsUnit (colMat α P).det := isUnit_iff_ne_zero.2 hdetA
    have hT := mem_Tsp_of_period hP₀ hP hM₀ (hαβ P hP) hdetA
    have hCofZ : Cof (Z P) = Cf P := by
      show (ι (π ((Cf P)ᵀ * M₀)) * M₀⁻¹)ᵀ = Cf P
      rw [hιπ _ hT, mul_nonsing_inv_cancel_right _ _ hu₀, transpose_transpose]
    refine ⟨show Cof (Z P) ∈ U by rw [hCofZ]; exact hCU, Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hu),
      fun x => ?_⟩
    rw [hQ, hCofZ]
    change P x = colMat α P *ᵥ realMap 1 ((colMat α P)⁻¹ * colMat β P) (P₀ x)
    rw [hαβ P hP x, realMap_apply, realMap_apply, one_mulVec, mulVec_add, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hu]
  · intro P P' hP hP' _ _ h hh
    let H := LinearMap.toMatrix' h.toLinearMap
    have hHv : ∀ v, h v = H *ᵥ v := fun v => (LinearMap.toMatrix'_mulVec _ v).symm
    have hHinv : LinearMap.toMatrix' h.symm.toLinearMap * H = 1 := by
      rw [← LinearMap.toMatrix'_comp, show h.symm.toLinearMap ∘ₗ h.toLinearMap = LinearMap.id from
        LinearMap.ext fun v => h.symm_apply_apply v, LinearMap.toMatrix'_id]
    have hHu : IsUnit H.det := isUnit_det_of_left_inverse hHinv
    have key : colMat α P' = H * colMat α P ∧ colMat β P' = H * colMat β P :=
      realMap_inj (ext_per hP₀ fun x => by
        rw [← hαβ P' hP' x, hh x, hαβ P hP x, hHv]
        simp only [realMap_apply, mulVec_add, mulVec_mulVec])
    show π (((colMat α P')⁻¹ * colMat β P')ᵀ * M₀) = π (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀)
    rw [key.1, key.2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H⁻¹ H, nonsing_inv_mul _ hHu,
      Matrix.one_mul]
  · intro m B' P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B' :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb)).1))
    refine differentiableOn_pi.2 fun k => ?_
    show DifferentiableOn ℂ (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) B'
    have hd : DifferentiableOn ℂ (fun b => ∑ i : Fin g, ∑ j : Fin g,
        (∑ l : Fin g, (∑ n : Fin g, (colMat α (P b))⁻¹ l n * colMat β (P b) n i) * M₀ l j) *
          π (Matrix.single i j 1) k) B' :=
      DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (DifferentiableOn.fun_sum fun l _ => (DifferentiableOn.fun_sum fun n _ =>
          (hinv _ _).mul (hc β _ _)).mul_const _).mul_const _
    apply hd.congr
    intro b _
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
      (coords_sum π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k)

end

end GlobalTheory.PerCoordU
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (exact GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (intros; apply GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lie_representation_spectral_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  first | exact @GlobalTheory.UPel.HT.LieProj.lie_projectors | exact GlobalTheory.UPel.HT.LieProj.lie_projectors | (intros; apply GlobalTheory.UPel.HT.LieProj.lie_projectors <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_perCl {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hR : K.Rich) (hB : K.Based) (c : H1 K.Oc) : ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective K.Oc c
  obtain ⟨G, hG⟩ := GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based K hR hB f.1 (fun T T' T'' φ ψ _ _ ↦ f.2 φ ψ)
  let f' : Z1 K.Oc := f - ⟨d0 K.Oc G, commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc G⟩
  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), f'.1 T T' φ = f.1 T T' φ - (G T' - φ.φ (G T)) :=
    fun _ _ _ ↦ rfl
  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → f'.1 T T' φ = 0 := by
    intro T T' φ hφ
    rw [hv, hG T T' φ hφ, sub_self]
  have hc : ∀ {T T' T'' : K.Obj} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f'.1 T T'' (φ ≫ ψ) = ψ.φ (f'.1 T T' φ) + f'.1 T' T'' ψ := fun φ ψ ↦ f'.2 φ ψ
  have hp : ∀ l : Λ, ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l →
      f'.1 T T' φ = algebraMap (Hol F.V) T'.C p :=
    fun l ↦ GlobalTheory.T.invariant_cochainOne_const_on_degree K hR f'.1 l
      (fun T T' T'' φ ψ _ hψ ↦ by rw [hc, h0 _ _ ψ hψ, add_zero])
      (fun T T' T'' φ ψ hφ _ ↦ by rw [hc, h0 _ _ φ hφ, map_zero, zero_add])
  choose p hp using hp
  have hcom : ∀ {T T' : K.Obj} (ψ : T ⟶ T') (x : Hol F.V),
      ψ.φ (algebraMap (Hol F.V) T.C x) = algebraMap (Hol F.V) T'.C x := fun ψ x ↦ ψ.φ.commutes x
  have hadd : ∀ l m, p (l + m) = p l + p m := by
    intro l m
    rw [← sub_eq_zero]
    refine GlobalTheory.T.parameter_function_eq_zero_of_composable K hR l m _ fun k k' k'' hl hm ↦ ?_
    let φ : K.triv k ⟶ K.triv k' := ptHom (K.triv k') hl
    let ψ : K.triv k' ⟶ K.triv k'' := ptHom (K.triv k'') hm
    have e := hc φ ψ
    rw [hp (l + m) _ _ (φ ≫ ψ) rfl, hp l _ _ φ rfl, hp m _ _ ψ rfl, hcom ψ] at e
    change K.cst k'' (p (l + m)) = K.cst k'' (p l) + K.cst k'' (p m) at e
    rw [(K.cst k'').map_sub, (K.cst k'').map_add, e, sub_self]
  refine ⟨AddMonoidHom.mk' p hadd, ?_⟩
  rw [perCl, H1.mk_eq_mk]
  refine ⟨G, ?_⟩
  funext T T' φ
  have e := hp φ.deg T T' φ rfl
  rw [hv] at e
  change G T' - φ.φ (G T) = f.1 T T' φ - algebraMap (Hol F.V) T'.C (p φ.deg)
  rw [← e]
  ring

end GlobalTheory.AnPer.Charts
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_ideal_section_integralFiniteIdele_upToUnits : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  first | exact @GlobalTheory.CMVal.exists_idele_section_of_ideal | exact GlobalTheory.CMVal.exists_idele_section_of_ideal | (intros; apply GlobalTheory.CMVal.exists_idele_section_of_ideal <;> assumption)
end
