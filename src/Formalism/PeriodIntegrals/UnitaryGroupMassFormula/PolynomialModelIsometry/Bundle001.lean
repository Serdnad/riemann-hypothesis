module

public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon
public import Formalism.PeriodIntegrals.Bundle021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExtLem
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Formalism.LocalRingCardinality.Params

@[expose] public section

section

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem polyExt_of (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PolyExt := by
  intro N H _ _ σ S hσ hfin hS
  classical
  let d := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  have hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)
  choose k P hkP using hc
  let K : ℕ := ∑ p : Fin d × Fin d, k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  let Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ := fun i j => P i j * detPoly N ^ (K - k i j)
  have hQ : ∀ g ∈ Kset (allPos N), ∀ i j,
      evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ := by
    intro g hg i j
    have e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j) := by
      rw [← pe_evM_detPoly g]
      simp only [Q, evM, map_mul, map_pow]
    rw [e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hk i j), mul_comm]
  let Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ := fun g => Matrix.of fun i j => evM g (Q i j)
  let Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S) := fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)
  have hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H) := by
    intro g hg x
    have key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype) := by
      refine b.toBasis.ext fun j => ?_
      have hmem : σ g ((b j : S) : H) ∈ S := hS g hg _ (b j).2
      have hsum := b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)
      have hsumH := congrArg (fun y : S => (y : H)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH
      show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) =
        g.det ^ K • σ g ((b.toBasis j : S) : H)
      rw [Matrix.toLin_self]
      simp only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]
      conv_rhs => rw [← hsumH]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ g hg i j, smul_smul]
    exact congrArg (fun f : S →ₗ[ℂ] H => f x) key
  have hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h := by
    intro g hg h hh
    ext x
    rw [LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]
  have hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h := by
    intro g hg h hh
    apply (Matrix.toLin b.toBasis b.toBasis).injective
    rw [Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
    exact hPlmul g hg h hh
  have hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h := by
    intro h hh g
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_right h (Q i j)
    let D := Q' - ∑ r, Q i r * C (Pm h r j)
    have hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j := by
      intro g'

      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]
    have := hD g
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  have hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h := by
    intro g h
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_left g (Q i j)
    let D := Q' - ∑ r, C (Pm g i r) * Q r j
    have hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j := by
      intro h'

      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]
    have := hD h
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  refine ⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩
  · intro g h
    show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _
    rw [hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
  · ext x
    rw [hA 1 (pe_one_mem N), hσ.1.1]
    simp
  · intro x y
    let fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)
    refine ⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩
    have hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g) := rfl
    rw [hf, Matrix.matrix_eq_sum_single (Pm g)]

    simp only [map_sum, evM, map_mul, eval_C]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rfl

end PI.WMI
end
end

section

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

lemma det_ne_zero_of_mem_K {N : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) :
    g.det ≠ 0 := by
  have h1 := hg.1
  rw [Matrix.mem_unitaryGroup_iff] at h1
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

lemma detPoly_ne_zero (N : ℕ) : detPoly N ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) h
  rw [detPoly, RingHom.map_det, map_zero] at this
  have hm : (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext i j; simp
  rw [hm, det_one] at this
  exact one_ne_zero this

lemma rowAct_detPoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    rowAct ℂ (n := N) A (detPoly N) = C A.det * detPoly N := by
  have h1 : (rowAct ℂ (n := N) A).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix A *
        Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ) := by
    ext i j
    simp [rowAct, Matrix.mul_apply]
  rw [detPoly, AlgHom.map_det, h1, Matrix.det_mul, ← RingHom.map_det]

theorem modelIso_of_steps (hA : PolyExt) (hI : LamInt) (hT : TorusEig) (hL : LowerInv)
    (hM : ModelMap) (hD : DetSplit) (hH : PI.HwIrred) : PI.ModelIso := by
  intro N Λ H _ _ σ S hU hK
  obtain ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩ := hK
  have hK' : IsKTypeOf (allPos N) σ Λ S := ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩
  haveI := hfin
  obtain ⟨K, P, hP, hPσ⟩ := hA N H σ S hU hfin hstab
  choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w
  let w0 : S := ⟨v0, hv0S⟩
  have hw0ne : w0 ≠ 0 := by
    intro h; apply hv0ne
    have := congrArg Subtype.val h
    simpa [w0] using this
  have hT' := hT N Λ H σ S K P hU hstab hPσ w0 hv0w
  have hL' := hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w
  have hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ := by
    intro θ x; rw [hT' θ x]; simp only [hμ]
  obtain ⟨ν, F, hν, hFmem, hF0, hFint⟩ := hM N S P w0 μ K hP hw0ne hT'' hL'
  have hanti : Antitone ν := by
    intro l j hlj
    by_contra hlt
    push_neg at hlt
    rcases eq_or_lt_of_le hlj with h | h
    · subst h; exact lt_irrefl _ hlt
    · have hbot := dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩
      have := hFmem w0
      rw [hbot, Submodule.mem_bot] at this
      exact hF0 this
  have hμanti : Antitone μ := by
    intro a b hab
    have h1 := hν a
    have h2 := hν b
    have h3 : (ν b : ℤ) ≤ ν a := by exact_mod_cast hanti hab
    omega
  let lam : DomWeight N := ⟨μ, hμanti⟩
  refine ⟨lam, fun a => hμ a, ?_⟩
  let c : ℕ := if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0
  have hnat : ∀ a, lam.natW a + c = ν a := by
    intro a
    have hN : 0 < N := a.pos
    have h1 := hν a
    have h2 := hν ⟨N - 1, by omega⟩
    have h3 : ν ⟨N - 1, by omega⟩ ≤ ν a := hanti (by rw [Fin.le_def]; simp; omega)
    have h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a := by exact_mod_cast h3
    simp only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]
    omega
  have hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 := by
    intro h; simp [DomWeight.natW, DomWeight.detShift, h, lam]
  have hsplit := hD N lam.natW c hlast
  have hνeq : (fun a => lam.natW a + c) = ν := funext hnat
  have hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c) := by
    intro x; rw [hνeq]; exact hFmem x
  let mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
    LinearMap.mulLeft ℂ (detPoly N ^ c)
  have hmulD_inj : Function.Injective mulD := by
    intro f g hfg
    simp only [mulD, LinearMap.mulLeft_apply] at hfg
    exact mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg
  let U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD
  have hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U := by
    intro g f hf
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · unfold sqAct
      exact Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)
    · set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef
      have hdg : dg ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
        ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)
      rw [map_smul, hFint, hx]
      simp only [mulD, LinearMap.mulLeft_apply, sqAct]
      rw [map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]
      have key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ) := by
        rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]
      simp only [smul_eq_C_mul, C_mul]
      linear_combination (C (detPow ℂ N g lam.detShift) * detPoly N ^ c *
        rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key
  obtain ⟨f0, hf0mem, hf0eq⟩ := hsplit (F w0) (hFmem' w0)
  have hf0U : f0 ∈ U := Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr
    (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩
  have hf0ne : f0 ≠ 0 := by
    intro h; apply hF0; rw [hf0eq, h, mul_zero]
  have hUeq : U = nablaSq ℂ N lam := by
    rcases (hH N lam).2.1 U inf_le_left hUst with h | h
    · exfalso; rw [h, Submodule.mem_bot] at hf0U; exact hf0ne hf0U
    · exact h
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ H := (LinearMap.ker F).map S.subtype
    have hS'le : S' ≤ S := by
      rintro _ ⟨y, _, rfl⟩; exact y.2
    have hS'st : IsKStableOn (allPos N) σ S' := by
      rintro g hg _ ⟨y, hy, rfl⟩
      have hd : g.det ^ K ≠ 0 := pow_ne_zero _ (det_ne_zero_of_mem_K hg)
      refine ⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
        rw [map_smul, hFint, hy, map_zero, smul_zero]
      · simp only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul,
          inv_mul_cancel₀ hd, one_smul]
    rcases hirr S' hS'le hS'st with h | h
    · rw [eq_bot_iff]
      intro y hy
      have hyS : (y : H) ∈ S' := ⟨y, hy, rfl⟩
      rw [h, Submodule.mem_bot] at hyS
      rw [Submodule.mem_bot]
      exact Subtype.ext hyS
    · exfalso
      have hv : v0 ∈ S' := by rw [h]; exact hv0S
      obtain ⟨y, hy, hyv⟩ := hv
      have hyw : y = w0 := Subtype.ext hyv
      rw [hyw] at hy
      exact hF0 hy
  let φ : U →ₗ[ℂ] LinearMap.range F :=
    LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype)
      (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      have := congrArg Subtype.val huv
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
      exact Subtype.ext (hmulD_inj this)
    · rintro ⟨z, x, rfl⟩
      obtain ⟨f', hf'mem, hf'eq⟩ := hsplit (F x) (hFmem' x)
      refine ⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr
        (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD,
        LinearMap.mulLeft_apply]
      exact hf'eq.symm
  calc Module.finrank ℂ S = Module.finrank ℂ (LinearMap.range F) :=
        (LinearMap.finrank_range_of_inj hFinj).symm
    _ = Module.finrank ℂ U := (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
    _ = Module.finrank ℂ (nablaSq ℂ N lam) := (LinearEquiv.ofEq _ _ hUeq).finrank_eq

end PI.WMI
end
end

section

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem lambda_integrality : LamInt := by
  intro N Λ H _ _ σ v hU hv hw a
  have hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I))
      = fun _ => (1 : ℂ) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [hb]
  have hmem := lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))
  have h := hw (Pi.single a (2 * Real.pi)) hmem
  rw [hfun, Matrix.diagonal_one, hU.1.1] at h
  have hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi) := by
    simp [Pi.single_apply]
  rw [hsum] at h
  have he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    apply hv
    have h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (Λ a : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem torus_eigenvalue_formula : TorusEig := by
  intro N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x
  have hwt : σ (torus (-θ)) (v0 : H) =
      Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
    hw (-θ) (lowerInv_torus_mem (-θ))
  have hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
    rw [torus, Matrix.det_diagonal]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right,
    lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end PI.WMI
end
end
