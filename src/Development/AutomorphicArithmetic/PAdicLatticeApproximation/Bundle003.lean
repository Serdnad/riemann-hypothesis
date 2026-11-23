module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

theorem UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D) {j : D'.La →+ VQ D},
        (∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u) → (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) →
        ∀ {f : ℕ → D.La →+ D'.La}, (∀ n : ℕ, 0 < n → n.Coprime p → ∀ (c : D.O) a, ∃ e, f n (c • a) = c • f n a + n • e) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w) → ∀ b : D.O,
        (T.toLinearMap.baseChange (AfP p)) * A * (actQ D b).baseChange (AfP p) =
          (actQ D b).baseChange (AfP p) * ((T.toLinearMap.baseChange (AfP p)) * A) := by
  intro p _ D D' ψ T j hj hjc f hf A hAL hA b
  let Cq : VQ D →ₗ[ℚ] VQ D := T.symm.toLinearMap ∘ₗ actQ D b ∘ₗ T.toLinearMap
  let Cc : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := Cq.baseChange (AfP p)
  have hC1 : ∀ u, Cq ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = (1 : ℚ) ⊗ₜ[ℤ] ψ (b • u) := by
    intro u
    have h : T ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) = actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) := by
      rw [hj, hj, hjc]
    change T.symm (actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u))) = _
    rw [← h, T.symm_apply_apply]
  have hCt : ∀ (a : AfP p) (u : D'.La), Cc (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) =
      a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) := by
    intro a u
    change Cq.baseChange (AfP p) _ = _
    rw [LinearMap.baseChange_tmul, hC1]
  have hCin : ∀ u, Cc (inAf D (ψ u)) = inAf D (ψ (b • u)) := fun u => hCt 1 u
  have hCL : ∀ v ∈ LaHat D, Cc v ∈ LaHat D := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [hCt]
      exact AddSubgroup.subset_closure ⟨a, ψ (b • u), ha, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hAC : A * (actQ D b).baseChange (AfP p) = Cc * A := by
    refine ext_inAf D fun x => ?_
    have := modZero D ((A * (actQ D b).baseChange (AfP p)) (inAf D x) - (Cc * A) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hA n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := hA n hn hc x
      obtain ⟨z, hz⟩ := hf n hn hc b x
      refine ⟨inAf D (ψ z) + w - Cc w', sub_mem (add_mem (inAf_mem D _) hw) (hCL _ hw'), ?_⟩
      rw [mul_apply_eq_comp, mul_apply_eq_comp, bc_inAf, e, hz, e', map_add (f := _), map_add (f := _), hCin, map_nsmul,
        map_nsmul, inAf_add, inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have hTC : (T.toLinearMap.baseChange (AfP p)) * Cc =
      (actQ D b).baseChange (AfP p) * (T.toLinearMap.baseChange (AfP p)) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a m =>
      change T.toLinearMap.baseChange (AfP p) (Cq.baseChange (AfP p) (a ⊗ₜ[ℚ] m)) =
        (actQ D b).baseChange (AfP p) (T.toLinearMap.baseChange (AfP p) (a ⊗ₜ[ℚ] m))
      simp only [LinearMap.baseChange_tmul]
      congr 1
      change T (T.symm (actQ D b (T m))) = actQ D b (T m)
      exact T.apply_symm_apply _
  rw [_root_.mul_assoc, hAC, ← _root_.mul_assoc, hTC, _root_.mul_assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem formIntegral {p : ℕ} [Fact p.Prime] {D : Datum p}
    (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ)
    (hF : ∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p))
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : IsIntAf (F v w) := by
  have ez : ∀ (a : AfP p) (x : D.La), a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
    intro a x
    rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hgen : ∀ (a : AfP p) (x : D.La), IsIntAf a → ∀ w ∈ LaHat D, IsIntAf (F (a • inAf D x) w) := by
    intro a x ha w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      rw [ez, map_smul, map_smul, LinearMap.smul_apply, hF, smul_eq_mul, smul_eq_mul]
      exact isInt_mul ha' (isInt_mul ha (isInt_intCast _))
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [ez]
    exact hgen a x ha w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

theorem UpperTheory.form_scalar_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ),
        (∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p)) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) → ∀ (gs : ℕ → D.La →+ D.La),
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (gs n x) + n • w) →
        ∀ (nu : ℕ → ℤ) (c : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ c = (nu n : AfP p) + n • b) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ e (gs n x) (gs n y) - nu n * (2 * D.EF x y)) →
        ∀ v w, F (A v) (A w) = (2 * c) * formAf D v w := by
  intro p _ D F e hF A _ gs hA nu c hc hsim
  have key : ∀ x x', F (A (inAf D x)) (A (inAf D x')) = (2 * c) * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (F (A (inAf D x)) (A (inAf D x')) - (2 * c) * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e₁⟩ := hA n hn hnp x
      obtain ⟨w', hw', e₂⟩ := hA n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := hsim n hn hnp x x'
      refine ⟨(k : AfP p) + F (inAf D (gs n x)) w' + F w (inAf D (gs n x')) +
        n • F w w' - (2 : ℤ) * β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formIntegral F e hF (inAf_mem D _) hw')) (formIntegral F e hF hw (inAf_mem D _)))
          (isInt_nsmul (formIntegral F e hF hw hw') n))
          (isInt_mul (isInt_mul (isInt_intCast 2) hβ) (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e₁, e₂, eβ]
        simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, hF, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have e2 := bilinear_ext_adelic_inclusion D (f := F.compl₁₂ A A) (g := (2 * c) • formAf D) fun x x' => by
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
  intro v w
  have := LinearMap.congr_fun₂ e2 v w
  simpa using this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem trivCore {A S : Type} [CommRing A] [Ring S] [Algebra A S] (σ : S → S)
    (hm : ∀ a b, σ (a * b) = σ b * σ a) (hs : ∀ x, σ (σ x) = x)
    (ha : ∀ r, σ (algebraMap A S r) = algebraMap A S r)
    (B b y y' : S) (hBb : B * b = 1) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (u t : A) (hut : t * u = 1)
    (h : σ (B * y) * y = algebraMap A S u) : y' * b * σ y' = algebraMap A S t := by
  have s1 : σ 1 = 1 := by
    have h0 := ha 1
    rwa [map_one] at h0
  have hσ : σ y' * σ y = 1 := by rw [← hm, h₂, s1]
  have hσ' : σ y * σ y' = 1 := by rw [← hm, h₁, s1]
  have hU : σ y * B * y = algebraMap A S u := by
    have h3 := congrArg σ h
    rw [hm, hs, ha] at h3
    rw [_root_.mul_assoc]
    exact h3
  have hB : B = σ y' * algebraMap A S u * y' := by
    rw [← hU]
    calc B = (σ y' * σ y) * B * (y * y') := by rw [hσ, h₂, _root_.one_mul, _root_.mul_one]
      _ = σ y' * (σ y * B * y) * y' := by simp only [_root_.mul_assoc]
  have e1 : algebraMap A S u * (σ y' * y' * b) = 1 := by
    rw [← hBb, hB, (Algebra.commutes u (σ y')).symm]
    simp only [_root_.mul_assoc]
  have hX : σ y' * y' * b = algebraMap A S t := by
    calc σ y' * y' * b = (algebraMap A S t * algebraMap A S u) * (σ y' * y' * b) := by
          rw [← map_mul, hut, map_one, _root_.one_mul]
      _ = algebraMap A S t := by rw [_root_.mul_assoc, e1, _root_.mul_one]
  calc y' * b * σ y' = (σ y * σ y') * y' * b * σ y' := by rw [hσ', _root_.one_mul]
    _ = σ y * (σ y' * y' * b) * σ y' := by simp only [_root_.mul_assoc]
    _ = σ y * algebraMap A S t * σ y' := by rw [hX]
    _ = algebraMap A S t * (σ y * σ y') := by rw [← Algebra.commutes, _root_.mul_assoc]
    _ = algebraMap A S t := by rw [hσ', _root_.mul_one]

private theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (x : R ⊗[ℚ] G.C) : (starT G.star R (starT G.star R x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]

private theorem starT_alg {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (r : R) : (starT G.star R (algebraMap R (R ⊗[ℚ] G.C) r)).unop = algebraMap R (R ⊗[ℚ] G.C) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, starT_tmul, map_one, MulOpposite.unop_one]

theorem UpperTheory.exists_unit_triv_of_similitude_factor :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y y' : AfP p ⊗[ℚ] G.C) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (s : ℚ),
        0 < s → ∀ (c : (AfP p)ˣ),
        (∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
          (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w) →
        ∃ t : (AfP p)ˣ, Triv G (AfP p) β ⟨y', y, h₁, h₂⟩ t := by
  intro p _ D G L β y y' h₁ h₂ s hs0 c hyp
  have hs : s ≠ 0 := ne_of_gt hs0
  set Bi := inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C) with hBi
  set b := inC G (AfP p) (β : G.C) with hb
  have hBb : Bi * b = 1 := by
    rw [hBi, hb, ← map_mul, Units.inv_mul, map_one]
  let u : AfP p := algebraMap ℚ (AfP p) (2 * s⁻¹) * (c : AfP p)
  let t : AfP p := algebraMap ℚ (AfP p) (s / 2) * ((c⁻¹ : (AfP p)ˣ) : AfP p)
  have hut : t * u = 1 := by
    have hq : s / 2 * (2 * s⁻¹) = 1 := by field_simp
    calc t * u = algebraMap ℚ (AfP p) (s / 2 * (2 * s⁻¹)) * (((c⁻¹ : (AfP p)ˣ) : AfP p) * c) := by
          simp only [t, u, map_mul]
          ring
      _ = 1 := by rw [hq, map_one, Units.inv_mul, _root_.one_mul]
  have htu : u * t = 1 := by rw [_root_.mul_comm]; exact hut
  let σ : AfP p ⊗[ℚ] G.C → AfP p ⊗[ℚ] G.C := fun x => (starT G.star (AfP p) x).unop
  have hkey : σ (Bi * y) * y = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) u := by
    apply GlobalTheory.AdelicSim.inj L
    apply LinearMap.ext
    intro w
    rw [AlgHom.commutes, Module.algebraMap_end_apply, ← sub_eq_zero]
    apply nondeg D
    intro v
    rw [map_sub, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
    simp only [σ]
    rw [← adjAf L, map_mul, Module.End.mul_apply]
    have hsinv : algebraMap ℚ (AfP p) s⁻¹ * algebraMap ℚ (AfP p) s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    calc _ = algebraMap ℚ (AfP p) s⁻¹ * (algebraMap ℚ (AfP p) s *
            formAf D (actOn L.rep (AfP p) Bi (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w))
            - u * formAf D v w := by
          rw [← _root_.mul_assoc, hsinv, _root_.one_mul]
      _ = 0 := by
          rw [hyp v w]
          simp only [u]
          rw [map_mul, map_ofNat]
          ring
  refine ⟨⟨t, u, hut, htu⟩, ?_⟩
  exact trivCore σ (fun a a' => by simp only [σ]; rw [map_mul, MulOpposite.unop_mul])
    (starT_invol G (AfP p)) (starT_alg G (AfP p)) Bi b y y' hBb h₁ h₂ u t hut hkey
end
