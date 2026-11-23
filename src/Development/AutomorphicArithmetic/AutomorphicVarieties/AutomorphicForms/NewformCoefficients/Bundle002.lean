module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.Bounds
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Sd
open scoped Matrix

namespace UpperTheory.V.Af.Nf

variable {F : Type} [Field F] [NumberField F]

private def sInt (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletionIntegers F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, Subring.mem_iInf.2 fun v => by
    classical
    change Pi.single (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w (x : w.adicCompletion F) v ∈
      v.adicCompletionIntegers F
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same]
      exact x.2
    · rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) _ _)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) _ _)

private theorem val_le (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) :
    Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-(c : ℤ)) := by
  induction c generalizing x with
  | zero => exact x.2
  | succ c ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun a b ha hb => ?_
    · have h1 : Valued.v (b : w.adicCompletion F) < 1 :=
        (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb
      have h2 : Valued.v (b : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        generalize Valued.v (b : w.adicCompletion F) = t at h1
        induction t using WithZero.expRecOn with
        | zero => exact zero_le
        | exp n =>
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
          rw [WithZero.exp_le_exp]
          omega
      have h3 : WithZero.exp (-((c + 1 : ℕ) : ℤ)) = WithZero.exp (-(c : ℤ)) * WithZero.exp (-1 : ℤ) := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring
      rw [h3]
      exact (map_mul _ (a : w.adicCompletion F) b).le.trans (mul_le_mul' (ih a ha) h2)
    · exact (Valuation.map_add_le _ ha hb)

private theorem nat_dvd (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : 1 ≤ M) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ ordI w (Ideal.span {(M : 𝓞 F)})) :
    (M : w.adicCompletionIntegers F) ∣ x := by
  have hM0 : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : Valued.v (M : w.adicCompletion F) = WithZero.exp (-(ordI w (Ideal.span {(M : 𝓞 F)}) : ℤ)) := by
    have : (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M) := by simp
    rw [this]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)
    refine h2.trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hM0]
    rfl
  have h0 : (M : w.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  refine ⟨⟨(M : w.adicCompletion F)⁻¹ * x, ?_⟩, Subtype.ext ?_⟩
  · change Valued.v ((M : w.adicCompletion F)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, h1]
    exact (inv_mul_le_one₀ WithZero.exp_pos).2 (val_le w _ x hx)
  · simp [h0]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.kLocal :
    UpperTheory.V.Af.Nf.KLocal := by
  rintro M hM w _ ⟨k, hk, rfl⟩
  refine ⟨cornerGL 2 (sInt w) k, ?_, ?_⟩
  · refine funext fun j => ?_
    have h0 : ![0, 1] ᵥ* (k.val.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w))) = ![0, 1] := hk
    have h1 := congrFun h0 j
    have h2 : k 1 j - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w := by
      rw [← Ideal.Quotient.eq]
      fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h1
    obtain ⟨y, hy⟩ := nat_dvd w hM _ h2
    have h3 : (cornerGL 2 (sInt w) k) 1 j - (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j ∈ Ideal.span {(M : ↥(Ohat ℚ))} := by
      have h4 : (cornerGL 2 (sInt w) k) 1 j = (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j -
          sInt w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j) + sInt w (k 1 j) := rfl
      rw [h4, sub_add_eq_add_sub, add_sub_assoc, add_sub_cancel_left, ← map_sub, hy, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [← Ideal.Quotient.eq] at h3
    fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h3
  · ext i j : 2
    change ((1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) i j : Af ℚ) -
        sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) i j) + sLoc ℚ w _ =
      (1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j - sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) + sLoc ℚ w _
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.one_apply_ne h]
      rfl
end
end

section

open UpperTheory.V in
theorem UpperTheory.V.Af.Nf.split :
    UpperTheory.V.Af.Nf.Split := by
  intro F _ _ _ a φ hφ hmem
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem
  have hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V) := by
    intro t o x hx
    have : (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o) :=
      iSup₂_le fun π hπ y hy =>
        (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)
    exact this hx
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hs) hφ
  | insert π t _ ih =>
    by_cases ht : φ ∈ ⨆ π ∈ t, π.V
    · exact ih ht
    rw [Finset.iSup_insert] at hs
    obtain ⟨ψ, hψ, w, hw, e⟩ := Submodule.mem_sup.1 hs
    rcases π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left
      (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h
    · refine ⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩
      · intro h0
        have h1 : ψ = 0 := congrArg Subtype.val h0
        rw [h1, zero_add] at e
        exact ht (e ▸ hw)
      · rw [← e]
        simpa using hw
    · exact absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht
end

section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.CuspRep in
theorem UpperTheory.V.Af.Nf.satComp :
    UpperTheory.V.Af.Nf.SatComp := by
  intro F _ _ _ φ π ψ W h0 hW hd hφ w B h
  have hle : ∀ g, W ≤ W.comap (locSm F w g) := fun g x hx => hW (.fin (locGL F 2 w g)) x hx
  have hi : Function.Injective (W.mkQ ∘ₗ π.V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.disjoint_iff_comap_eq_bot.1 hd
  have he : W.mkQ φ = (W.mkQ ∘ₗ π.V.subtype) ψ := (Submodule.Quotient.eq W).2 hφ
  have h1 := h.map (ρ' := (locSm F w).quotient W hle) W.mkQ (fun _ _ => rfl)
    (by rw [he]; exact fun e => h0 (hi (e.trans (map_zero _).symm)))
  rw [he] at h1
  exact GlobalTheory.LFun.IsSatVecGL.of_map _ (fun _ _ => rfl) hi h1
end

section

open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

private theorem nsl_pos (k : ℕ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    nsl k f g z = ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) := by
  have h : (((g.val 0 0 : ℝ) : ℂ) * z + g.val 0 1) / (((g.val 1 0 : ℝ) : ℂ) * z + g.val 1 1) = ((g • z : ℍ) : ℂ) := by
    rw [coe_smul_of_det_pos (by simpa using hg)]
    rfl
  unfold nsl
  rw [h, sign_pos hg, abs_of_pos hg]
  simp only [SignType.coe_one, Complex.ofReal_one, one_mul, ofComplex_apply, mul_assoc]
  rfl

private theorem nsl_slash (k : ℕ) (f : ℍ → ℂ) (x : GL (Fin 2) ℝ) (hx : 0 < x.val.det) :
    nsl k f x = (((x.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) • f ∣[(k : ℤ)] x := by
  funext z
  have hσ : σ x (f (x • z)) = f (x • z) := by simp [σ, hx]
  have hr : x.val.det ^ ((k : ℝ) / 2) = x.val.det ^ (1 - (k : ℝ) / 2) * x.val.det ^ ((k : ℤ) - 1) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  rw [nsl_pos k f x hx, Pi.smul_apply, ModularForm.slash_apply, hσ, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hx, hr, smul_eq_mul]
  push_cast
  ring

private theorem nsl_eps (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : nsl k f (eps * x) = nsl k f x := by
  funext z
  have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
  have h0 : ∀ j, (eps * x) 0 j = -x 0 j := fun j => by simp [eps, Matrix.mul_apply]
  have h1 : ∀ j, (eps * x) 1 j = x 1 j := fun j => by simp [eps, Matrix.mul_apply]
  unfold nsl
  rw [hd, h0, h0, h1, h1, abs_neg, Left.sign_neg]
  congr 3
  push_cast
  ring

private theorem nsl_mdiff_pos (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) :
    MDiff (nsl k f x) := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx.ne'
  have hg : 0 < g.val.det := hx
  have : nsl k f x = fun z : ℍ => ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) :=
    funext (nsl_pos k f g hg)
  rw [this]
  exact mdifferentiable_const.mul ((mdifferentiable_denom_zpow g _).mul
    (hf.comp (mdifferentiable_smul (by simpa using hg))))

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslSl :
    UpperTheory.V.Af.Nf.NslSl := by
  intro k f
  refine ⟨fun δ => ?_, nsl_slash k f, fun hf x hx => ?_⟩
  · have hv : (δ : GL (Fin 2) ℝ).val = δ.1.map (Int.cast : ℤ → ℝ) := rfl
    have hd : (δ : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ).det_coe
    rw [← hv, nsl_slash k f _ (by rw [hd]; exact one_pos), hd, ModularForm.SL_slash]
    simp
  · rcases hx.lt_or_gt with h | h
    · rw [← nsl_eps]
      refine nsl_mdiff_pos k f hf _ ?_
      have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
      rw [hd]; linarith
    · exact nsl_mdiff_pos k f hf x h
end

section

open NumberField Formalism.L2.Host UpperTheory.V UpperTheory.V.Af GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
open GlobalTheory.CuspRep (Af)

theorem UpperTheory.V.Af.Nf.absExpo :
    UpperTheory.V.Af.Nf.AbsExpo := by
  intro F _ _ _ s v
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]
end

section

open UpperTheory.V.Sd in
private theorem mem_mirab_iff {R : Type} [CommRing R] (g : GL (Fin 2) R) : g ∈ mirab R ↔ g 1 0 = 0 ∧ g 1 1 = 1 := by
  change Matrix.vecMul ![0, 1] (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1] ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Af.Nf.memK :
    UpperTheory.V.Af.Nf.MemK := by
  intro M g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 := ((mem_mirab_iff _).1 hk).1
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 := ((mem_mirab_iff _).1 hk).2
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ?_, ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) ↥(Ohat ℚ)) a b).2
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 e0)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e1)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨z, hz, e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (Ohat ℚ).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) ↥(Ohat ℚ) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (Af ℚ)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext e⟩)
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨z, hz⟩, Subtype.ext e'⟩)
    exact ⟨k, (mem_mirab_iff _).2 ⟨e0, e1⟩, Units.ext rfl⟩
end

section

open UpperHalfPlane hiding I
open CongruenceSubgroup

theorem UpperTheory.V.Af.Nf.archBd :
    UpperTheory.V.Af.Nf.ArchBd := by
  intro k M hM f
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun x hx => ?_⟩
  unfold UpperTheory.V.Af.Nf.nsl
  set J : ℂ := (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ) with hJdef
  set w : ℂ := (((SignType.sign x.det : ℝ)) : ℂ) *
    (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J) with hwdef
  have hJ0 : J ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [J] at h1 h2
    apply hx
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hn : Complex.normSq J = ‖J‖ ^ 2 := Complex.normSq_eq_norm_sq J
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJ0
  have hDpos : 0 < |x.det| := abs_pos.mpr hx
  have hq : (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J).im =
      x.det / Complex.normSq J := by
    rw [Complex.div_im, Matrix.det_fin_two]
    simp [J]
    ring
  have himw : w.im = |x.det| / ‖J‖ ^ 2 := by
    rw [hwdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq, hn]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [sign_neg h, abs_of_neg h]
      simp
      ring
    · rw [sign_pos h, abs_of_pos h]
      simp
  have hw : 0 < w.im := by
    rw [himw]
    positivity
  have hτ : (ofComplex w).im = |x.det| / ‖J‖ ^ 2 := by
    rw [← himw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    all_goals rfl
  have hb := hC (ofComplex w)
  rw [hτ] at hb
  have hpow : (|x.det| / ‖J‖ ^ 2) ^ (((k : ℤ) : ℝ) / 2) = |x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k := by
    rw [Real.div_rpow hDpos.le (by positivity), ← Real.rpow_natCast ‖J‖ 2,
      ← Real.rpow_mul hJpos.le]
    push_cast
    congr 1
    rw [show (2 : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by ring, Real.rpow_natCast]
  rw [hpow] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_zpow]
  calc _ ≤ |x.det| ^ ((k : ℝ) / 2) * ‖J‖ ^ (-(k : ℤ)) *
        (C / (|x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k)) := by gcongr
    _ = C := by
      have h1 : 0 < |x.det| ^ ((k : ℝ) / 2) := by positivity
      have h2 : 0 < ‖J‖ ^ k := by positivity
      rw [zpow_neg, zpow_natCast]
      field_simp
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w (n := 2)) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w (n := 2)) (KGL w (n := 2)) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w (n := 2) := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem UpperTheory.V.Af.Nf.satOfU :
    UpperTheory.V.Af.Nf.SatOfU := by
  intro F _ _ w V _ _ ρ x α β h0 hx hU hz
  rw [iwahori_level_zero_eq] at hx
  have hx' : x ∈ GlobalTheory.PRep.fixed ρ (KGL w (n := 2)) := GlobalTheory.LGrp.mem_fixed.2 hx
  refine ⟨h0, hx', rfl, fun ϖ hϖ j hj => ?_⟩
  rw [ExSatGL.Tj_indep j (ϖ := (atFin w (unif w) : w.adicCompletion F)) (unif_spec w) hϖ]
  interval_cases j
  · rw [ExSatGL.heckeVec_Tj_zero ρ _ hx']
    simp [satEig, Multiset.esymm]
  · rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ])] at hU
    rw [hU]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := by
      simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])]
    have ho : ∀ q ∈ MulAction.orbit (KGL w (n := 2)) (z : _ ⧸ KGL w (n := 2)), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w (n := 2)) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton, hz]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
end
end
