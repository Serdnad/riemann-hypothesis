module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle001
public import GroundTheory.AutomorphicForms.ReductionDirichlet
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open UpperTheory.V.Sd.Eis

noncomputable section

open NumberField MeasureTheory Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem map_aff1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_one_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem infGL_aff (x : TR.Rinf F) : TR.infGL F 2 (aff 1 x) = aff 1 (TR.sInf F x) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL, map_aff1]
    exact congrArg _ ((TR.infEq F).symm_apply_apply x).symm
  · rw [TR.pFin_infGL, map_aff1]
    exact aff_one_zero.symm

private theorem infGL_left (a : GL (Fin 2) (TR.Rinf F)) (g : GA F 2) :
    TR.infGL F 2 a * g = g * TR.infGL F 2 ((GeneralLinearGroup.map (TR.pInf F) g)⁻¹ * a * GeneralLinearGroup.map (TR.pInf F) g) :=
  TR.ga_ext (by simp only [map_mul, map_inv, TR.pInf_infGL]; group) (by simp only [map_mul, map_inv, TR.pFin_infGL]; group)

omit [IsTotallyReal F] in
private theorem conj_deriv (h : GL (Fin 2) (TR.Rinf F)) (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F))
    (ha : HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0) :
    HasDerivAt (fun t => TR.toL (h⁻¹ * a t * h).val) (TR.toL ((h⁻¹).val * X * h.val)) 0 :=
  ((TR.rmul (TR.toL h.val)).comp (TR.lmul (TR.toL (h⁻¹).val))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha

open Classical in
omit [IsTotallyReal F] in
private theorem conj_dec (h : GL (Fin 2) (TR.Rinf F)) (i j : Fin 2) (u : TR.Rinf F) :
    TR.toL ((h⁻¹).val * Matrix.single i j u * h.val) = ∑ v, u v • ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) •
          TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F)) := by
  funext a b w
  simp only [← map_inv]
  generalize h⁻¹ = h'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, Pi.single_apply, Finset.sum_apply] <;> ring

omit [IsTotallyReal F] in
private theorem nil_curve (u : TR.Rinf F) :
    Continuous (fun t : ℝ => aff (1 : (TR.Rinf F)ˣ) (t • u)) ∧
    (∀ s t : ℝ, aff (1 : (TR.Rinf F)ˣ) ((s + t) • u) = aff 1 (s • u) * aff 1 (t • u)) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (1 : (TR.Rinf F)ˣ) (t • u)).val) (TR.toL (Matrix.single 0 1 u)) 0 := by
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv] <;> fun_prop
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, add_smul, add_comm]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u

omit [IsTotallyReal F] in
private theorem tor_curve (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ) (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) :
    Continuous (fun t : ℝ => aff (y t) 0) ∧
    (∀ s t : ℝ, aff (y (s + t)) 0 = aff (y s) 0 * aff (y t) 0) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (y t) 0).val) (TR.toL (Matrix.single 0 0 u)) 0 := by
  have e : ∀ t, (y t).val = fun v => Real.exp (t * u v) := fun t => funext (hy t)
  have e' : ∀ t, ((y t)⁻¹).val = fun v => Real.exp (-(t * u v)) := fun t =>
    Units.inv_eq_of_mul_eq_one_right (by funext v; simp [hy, ← Real.exp_add])
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, e] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv, e'] <;> fun_prop
  · ext i j v
    fin_cases i <;> fin_cases j <;> simp [aff, hy, add_mul, Real.exp_add]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    refine hasDerivAt_pi.2 fun v => ?_
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (u v)).exp

theorem UpperTheory.eisenstein_continuous_left_action :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.CtBasic → UpperTheory.V.Sd.Eis.CtLie → UpperTheory.V.Sd.Eis.LieAlg → UpperTheory.V.Sd.Eis.CentLie → UpperTheory.V.Sd.Eis.CtLeft := by
  intro hS hB hL hA hC F _ _ _ _ _ μ _ D hD k c ω hω φ hφ u y hy g
  classical
  have hl := hL F μ D hD φ hφ.aut.left hφ.aut.level
  have hb := hB F μ D hD φ.1 (hS F 2 φ hφ.aut.level) hφ.aut.left
  have hi : ∀ X, IntegrableOn (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) D μ := fun X =>
    (hB F μ D hD _ (hl X).1.2 (hl X).1.1).1 g
  let L : TR.Lie F 2 →ₗ[ℝ] ℂ :=
    { toFun := fun X => cterm μ D (TR.lie F 2 X φ).1 g
      map_add' := fun X Y => by
        rw [map_add (f := _)]
        exact integral_add (hi X) (hi Y)
      map_smul' := fun r X => by
        rw [map_smul]
        exact integral_smul r (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) }
  have hsm : ∀ (X) (z : ℂ) (ψ : TR.Sm F 2), TR.lie F 2 X φ = z • ψ → L X = z * cterm μ D ψ.1 g := fun X z ψ e => by
    change cterm μ D (TR.lie F 2 X φ).1 g = _
    rw [e]
    exact integral_const_mul z (fun x : NA F => ψ.1 (unip x * g))
  set h := GeneralLinearGroup.map (TR.pInf F) g with hh
  have key : ∀ (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F)), Continuous a →
      (∀ s t, a (s + t) = a s * a t) → HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0 →
      HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (a t) * g)) (L (TR.toL ((h⁻¹).val * X * h.val))) 0 := by
    intro a X h1 h2 h3
    simp only [infGL_left _ g]
    exact (hl _).2 (fun t => h⁻¹ * a t * h) (by fun_prop) (fun s t => by rw [h2]; group) (conj_deriv h a X h3) g
  have hnil : ∀ x : TR.Rinf F, L (TR.toL ((h⁻¹).val * Matrix.single 0 1 x * h.val)) = 0 := fun x => by
    obtain ⟨h1, h2, h3⟩ := nil_curve x
    have := key _ _ h1 h2 h3
    simp only [infGL_aff, hb.2.1] at this
    exact this.unique (hasDerivAt_const _ _)
  let E : InfinitePlace F → Fin 2 → Fin 2 → TR.Lie F 2 := fun v a b => TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F))
  have hE : ∀ v a b, TR.lie F 2 (E v a b) = TR.Eop v a b := fun _ _ _ => by
    simp only [E, TR.Eop]
  have hdec : ∀ (i j : Fin 2) (x : TR.Rinf F), L (TR.toL ((h⁻¹).val * Matrix.single i j x * h.val)) =
      ∑ v, (x v : ℂ) * ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) * L (E v a b) := fun i j x => by
    rw [conj_dec]

    simp only [map_sum, map_smul, Complex.real_smul, E]
  have hv := fun v : InfinitePlace F => hA (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h) (fun a b => L (E v a b))
    (k * cterm μ D φ.1 g)
    (by
      rw [← map_add (f := _), hsm _ 0 φ, zero_mul]
      rw [map_add (f := _), hE, hE, zero_smul]
      exact hC F k c ω hω φ hφ v)
    (by
      rw [← map_sub, hsm _ (Complex.I * k) φ, mul_assoc]
      rw [map_sub, hE, hE]
      exact hφ.wt v)
    (by
      rw [← map_sub, ← map_add (f := _), hsm _ Complex.I (TR.lie F 2 (E v 0 1 + E v 1 0) φ)]
      · rfl
      rw [map_sub, map_add (f := _), hE, hE, hE, hE]
      exact hφ.low v)
    (by
      have := hnil (Pi.single v 1)
      rw [hdec, Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw]) (by simp)] at this
      simpa only [Pi.single_eq_same, Complex.ofReal_one, one_mul] using this)
  obtain ⟨h1, h2, h3⟩ := tor_curve u y hy
  have := key _ _ h1 h2 h3
  rw [hdec] at this
  simp only [hv] at this
  convert this using 1
  rw [← Finset.sum_mul]
  push_cast
  ring
end
end

section

open UpperTheory.V.Sd.Eis

theorem UpperTheory.eisenstein_central_lie_action :
    UpperTheory.V.Sd.Eis.CentLie :=
  fun F _ _ _ _ _ ω hω φ hφ v => UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v
end

section

open UpperTheory.V.Sd.Eis
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V

private theorem idele_split (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom x) * finId F (Units.map (pFin F).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h3, h4]

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) :
    Continuous fun x : Ad F => TR.pInf F x v :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
    ((continuous_apply v).comp continuous_fst)

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ray_class_group_finite :
    UpperTheory.V.Sd.Eis.RayFin := by
  intro F _ _ _ H hK hR hf
  have hopen : IsOpen (H : Set (Ideles F)) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    have c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ) :=
      Continuous.units_map _ continuous_snd
    have h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H := by
      have := c1.continuousAt (x := 1)
      rw [ContinuousAt, map_one] at this
      exact this hf
    have h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v := by
      rw [Filter.eventually_all]
      intro v
      have c : Continuous fun x : Ideles F => TR.pInf F x.val v := (cont_pInf F v).comp Units.continuous_val
      refine c.continuousAt.eventually (lt_mem_nhds ?_)
      simp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← idele_split F x]
    exact H.mul_mem (hR _ hx2) hx1
  refine ⟨hopen, ?_⟩
  have hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H := by
    intro ρ hρ
    set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz
    have e : Units.map (pFin F).toMonoidHom z = 1 := by
      refine Units.ext ?_
      ext v
      exact congrArg _ (posIdele_finite ρ hρ v)
    have e2 := idele_split F z
    rw [e, map_one, mul_one] at e2
    rw [← e2, ← map_pow]
    refine hR _ fun v => ?_
    set y := Units.map (TR.pInf F).toMonoidHom z
    have hy : y.val v ≠ 0 := by
      have := congrFun y.mul_inv v
      exact left_ne_zero_of_mul_eq_one this
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    positivity
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  have hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H := by
    intro t
    have hn : 2 * Module.finrank ℚ F ≠ 0 := mul_ne_zero two_ne_zero Module.finrank_pos.ne'
    have ht : 0 < (ideleModule F t : ℝ) := (ideleModule F t).2
    set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef
    have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
    have hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
    have hzH := hsq ρ hρ
    have hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t := by
      refine Subtype.ext ?_
      rw [sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]
      rfl
    generalize (posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt
    have h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1 := by
      rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
    obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
    refine ⟨_, hcS, ?_⟩
    have e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹ := by
      rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    rw [e]
    exact H.mul_mem hzH (H.inv_mem (hK c))
  haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen
  have hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  haveI : Finite (Ideles F ⧸ H) := by
    refine Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, hst⟩ := hcov t
    exact ⟨s, hs, QuotientGroup.eq.2 hst⟩
  exact Subgroup.finiteIndex_of_finite_quotient
end

section

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2
open scoped Matrix

section
variable {k : Type} [Field k]

private def nn (p q r s t : k) : M4 k := !![1, 0, 0, 0; p, 1, 0, 0; q, s, 1, 0; r, t, -p, 1]

private theorem adj_nn (p q r s t : k) :
    adj (nn p q r s t) = !![1, 0, 0, 0; -p, 1, 0, 0; -t, -s, 1, 0; -r, -q, p, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, nn, sgn, Fin.rev]

private theorem low_nn (p q r s t : k) (h : t + p * s - q = 0) : IsLow (nn p q r s t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    rw [adj_nn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nn, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | ring1 | linear_combination h | linear_combination -h
  · intro i
    fin_cases i <;> simp [nn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [nn]

private theorem par1 (u a a' : k) (A : Matrix (Fin 2) (Fin 2) k) (ha : a ≠ 0)
    (h : A *ᵥ ![u, 1] = a • ![u, 1]) (hd : A.det = a * a') :
    ∃ p, A = !![a' + u * p, (a - a' - u * p) * u; p, a - p * u] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : A 0 0 = a' + u * A 1 0 := by
    apply mul_left_cancel₀ ha
    linear_combination hd - A 0 0 * h1 + A 1 0 * h0
  refine ⟨A 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact h2
  · linear_combination h0 - u * h2
  · linear_combination h1

private theorem par2 (w b b' : k) (B : Matrix (Fin 2) (Fin 2) k) (hb : b ≠ 0)
    (h : B *ᵥ ![1, w] = b • ![1, w]) (hd : B.det = b * b') :
    ∃ q, B = !![b - q * w, q; (b - b' - q * w) * w, b' + q * w] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : B 1 1 = b' + B 0 1 * w := by
    apply mul_left_cancel₀ hb
    linear_combination hd - B 1 1 * h0 + B 0 1 * h1
  refine ⟨B 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination h0
  · linear_combination h1 - w * h2
  · exact h2

private theorem case1 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : 1 + γ * u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![u, 1] = a • ![u, 1]) (hB : B *ᵥ ![1, w] = b • ![1, w]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (γ * u) (-1) (γ * u) (-(2 * w) / (1 + γ * u * w)) (-(1 - γ * u * w) / (1 + γ * u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![a, b, b', a'] i := by
  obtain ⟨p, rfl⟩ := par1 u a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par2 w b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

private theorem case2 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : (γ : k) + u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![1, w] = a • ![1, w]) (hB : B *ᵥ ![u, 1] = b • ![u, 1]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (-u) 1 u (-(2 * w) / (γ + u * w)) ((γ - u * w) / (γ + u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![b, a, a', b'] i := by
  obtain ⟨p, rfl⟩ := par2 w a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par1 u b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

end

private theorem norm_add_one {k : Type} [NormedField k] [IsUltrametricDist k] (x y : k) (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    ‖x + y‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne'), hx]
  exact max_eq_left hy.le

private theorem norm_two_mul {k : Type} [NormedField k] [IsUltrametricDist k] (w : k) (hw : ‖w‖ < 1) :
    ‖2 * w‖ < 1 := by
  rw [two_mul]
  exact (IsUltrametricDist.norm_add_le_max w w).trans_lt (by simpa using hw)

private theorem lowQ_nn {l : ℕ} [Fact l.Prime] (p q r s t : Formalism.ConjugateSelfDual.Qbar l) (h : t + p * s - q = 0)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ = 1) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ < 1) (ht : ‖t‖ ≤ 1) : LowQ (nn p q r s t) := by
  refine ⟨low_nn p q r s t h, ?_, by simpa [nn] using hs, by simpa [nn] using hq⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nn, hp, hq.le, hr, hs.le, ht]

theorem UpperTheory.mix_flag_exists :
    UpperTheory.V.Sd.S2.MixFlag := by
  intro l _ _ γ u w hγ hu hw
  have huw : ‖u * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans_lt hw
  have hz : ‖γ * u * w‖ < 1 := by rw [mul_assoc, norm_mul, hγ, one_mul]; exact huw
  have h1 := norm_add_one 1 _ norm_one hz
  have h1' : ‖1 - γ * u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one 1 _ norm_one (by rwa [norm_neg])
  have h3 := norm_add_one _ _ hγ huw
  have h3' : ‖γ - u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one _ _ hγ (by rwa [norm_neg])
  have n1 : 1 + γ * u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have n3 : γ + u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h3; exact zero_ne_one h3
  have h2 := norm_two_mul w hw
  have hgu : ‖γ * u‖ ≤ 1 := by rw [norm_mul, hγ, one_mul]; exact hu
  refine ⟨⟨_, lowQ_nn (γ.val * u) (-1) (γ.val * u) (-(2 * w) / (1 + γ.val * u * w)) (-(1 - γ.val * u * w) / (1 + γ.val * u * w)) ?_ hgu
      (by simp) hgu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case1 two_ne_zero γ u w n1 A B a a' b b' ha hb hA hB dA dB _ rfl⟩,
    ⟨_, lowQ_nn (-u) 1 u (-(2 * w) / (γ.val + u * w)) ((γ.val - u * w) / (γ.val + u * w)) ?_ (by rwa [norm_neg])
      (by simp) hu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case2 two_ne_zero γ u w n3 A B a a' b b' ha hb hA hB dA dB _ rfl⟩⟩
  · field_simp; ring
  · rw [norm_div, norm_neg, h1, div_one]; exact h2
  · rw [norm_div, norm_neg, h1, h1', div_one]
  · field_simp; ring
  · rw [norm_div, norm_neg, h3, div_one]; exact h2
  · rw [norm_div, h3, h3', div_one]
end

section

theorem UpperTheory.complex_conjugations_are_conjugate :
    UpperTheory.V.Sd.S2.ConjCc := by
  intro Ω _ _ _ a b ha hb
  obtain ⟨j, hj⟩ := ha
  obtain ⟨j', hj'⟩ := hb
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j j'
    (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = j' x := fun x => by
    rw [← hσ]; rfl
  refine isConj_iff.2 ⟨σ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply j'.injective
  rw [hj', ← h, ← h]
  change j (σ.symm (σ (a (σ.symm x)))) = _
  rw [AlgEquiv.symm_apply_apply, hj]
end
