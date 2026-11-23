module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Topology.Algebra.Star.Unitary
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Lean.Meta.ExprDefEq

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd

namespace UpperTheory.V.Br.HolomorphicCuspFiniteness

private theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

private theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

end UpperTheory.V.Br.HolomorphicCuspFiniteness

open UpperTheory.V.Br.HolomorphicCuspFiniteness in
theorem UpperTheory.V.Br.holCuspFin : UpperTheory.V.Br.HolCuspFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hlev : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  refine ⟨⟨M, hM1, hlev⟩, ?_⟩
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (Complex.I * k * ∑ v, (θ v : ℂ))) dec
  haveI := cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun _ u => (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ k ∈ KLev F 2 M, TR.finRep F 2 k φ = φ) ∧
      (∀ g : GA F 2, (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ})
  have hφ' : IsHol k c ω φ := hφ.1
  refine ⟨hφ.2, hlev φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (holCap F k c ω hω φ hφ').2⟩
  have := UpperTheory.V.Br.rotEig F φ _ hφ'.wt θ (Unitary.toUnits (rot θ)) rfl (g * TR.infGL F 2 (Unitary.toUnits x))
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

section

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis
open scoped Matrix

namespace UpperTheory.V.Br.CuspStabilizer

section Aff
variable {R S : Type} [CommRing R] [CommRing S]

private theorem aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem corner_aff (s : R →ₙ+* S) (y : Rˣ) (x : R) : cornerGL 2 s (aff y x) = aff (Units.map (corner s) y) (s x) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (aff y x i j) = _
  fin_cases i <;> fin_cases j <;> simp [aff, corner]

private theorem continuous_aff [TopologicalSpace R] [IsTopologicalRing R] : Continuous fun y : Rˣ => aff y (0 : R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop

end Aff

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private def stab (M : ℕ) (g : GA F 2) : Subgroup (Ideles F) where
  carrier := {u | ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff (t * u) 0 * g ∈ Z ↔ aff t 0 * g ∈ Z}
  one_mem' := fun Z _ t => by rw [mul_one]
  mul_mem' := fun {a b} ha hb Z hZ t => by rw [← mul_assoc, hb Z hZ, ha Z hZ]
  inv_mem' := fun {a} ha Z hZ t => by rw [← ha Z hZ, inv_mul_cancel_right]

private theorem mem_stab {M : ℕ} {g : GA F 2} {u : Ideles F}
    (h1 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u) 0 * g ∈ Z)
    (h2 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u⁻¹) 0 * g ∈ Z) : u ∈ stab M g :=
  fun Z hZ t => ⟨fun h => by simpa only [mul_inv_cancel_right] using h2 Z hZ _ h, h1 Z hZ t⟩

private theorem stab_fin {M : ℕ} (hM : 1 ≤ M) (g : GA F 2) : (stab M g).FiniteIndex := by
  have am : ∀ t u : Ideles F, aff (t * u) (0 : Ad F) = aff u 0 * aff t 0 := fun t u => by rw [aff_mul, mul_comm]; simp
  have h1 : ∀ a : Fˣ, ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * diagUnits F a) 0 * g ∈ Z :=
    fun a Z hZ t h => by rw [am, mul_assoc]; exact hZ.rat a _ h
  have h2 : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * TR.infId F y) 0 * g ∈ Z := fun y hy Z hZ t h => by
    have := hZ.pos y hy _ h
    rw [TR.infGL, corner_aff, map_zero] at this
    rw [am, mul_assoc]; exact this
  set k := Matrix.GeneralLinearGroup.map (pFin F) g with hk
  have h3 : ∀ u : (Af F)ˣ, k⁻¹ * aff u 0 * k ∈ KLev F 2 M → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * finId F u) 0 * g ∈ Z := fun u hu Z hZ t h => by
    have e : aff (finId F u) 0 * g = g * finGL F 2 (k⁻¹ * aff u 0 * k) := by
      have : aff (finId F u) 0 = finGL F 2 (aff u 0) := by rw [finGL, corner_aff, map_zero]; rfl
      rw [this]
      exact TR.ga_ext (by simp) (by simp [k, mul_assoc])
    rw [mul_comm t, am, mul_assoc, e, ← mul_assoc]
    exact hZ.lev _ hu _ h
  refine (UpperTheory.ray_class_group_finite F (stab M g) (fun a => mem_stab (h1 a) ?_) (fun y hy => mem_stab (h2 y hy) ?_) ?_).2
  · rw [← map_inv]; exact h1 _
  · rw [← map_inv]
    refine h2 _ fun v => ?_
    have h : y.val v * (y⁻¹).val v = 1 := congrFun y.mul_inv v
    exact (mul_pos_iff_of_pos_left (hy v)).1 (h ▸ one_pos)
  · have h4 := ((isOpen_KLev (F := F) (n := 2) hM).preimage (f := fun u : (Af F)ˣ => k⁻¹ * aff u 0 * k)
      ((continuous_const.mul continuous_aff).mul continuous_const)).mem_nhds (x := 1) (by simp [aff_one])
    filter_upwards [h4] with u hu
    refine mem_stab (h3 u hu) ?_
    rw [← map_inv]
    refine h3 _ ?_
    have e : aff u⁻¹ (0 : Af F) = (aff u 0)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [aff_mul]; simp [aff_one])
    have := (KLev F 2 M).inv_mem hu
    rw [e]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this

end UpperTheory.V.Br.CuspStabilizer

open UpperTheory.V.Br.CuspStabilizer in
theorem UpperTheory.V.Br.cuspSet :
    UpperTheory.V.Br.CuspSet := by
  intro F _ _ _ M hM
  haveI : CompactSpace (KLev F 2 1) := isCompact_iff_compactSpace.1 (isCompact_KLev le_rfl)
  haveI : Finite (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ((isOpen_KLev hM).preimage continuous_subtype_val)
  let b : (InfinitePlace F → ℤˣ) × (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) → GA F 2 := fun p =>
    TR.infGL F 2 (Unitary.toUnits (eps p.1)) * finGL F 2 p.2.out.1
  haveI : ∀ g : GA F 2, (stab M g).FiniteIndex := stab_fin hM
  refine ⟨⋃ p, Set.range fun q : Ideles F ⧸ stab M (b p) => aff q.out 0 * b p,
    Set.finite_iUnion fun p => Set.finite_range _, fun Z hS hZ => Set.eq_univ_of_forall fun g => ?_⟩
  have h1 : ∀ p t, aff t 0 * b p ∈ Z := fun p t => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stab M (b p)) t
    refine (h.2 Z hZ t).1 ?_
    rw [← hh]
    exact hS (Set.mem_iUnion.2 ⟨p, _, rfl⟩)
  obtain ⟨z, y, x, r, u, hu, rfl⟩ := UpperTheory.V.Br.iwasawaA F g
  obtain ⟨s, θ, rfl⟩ := dec r
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KLev F 2 M).subgroupOf (KLev F 2 1)) ⟨u, hu⟩
  have h2 := hZ.lev _ ((KLev F 2 M).inv_mem h.2) _ (h1 (s, QuotientGroup.mk ⟨u, hu⟩) y)
  have h3 := hZ.cent z _ (hZ.unip x _ (hZ.rot θ (Unitary.toUnits (rot θ)) rfl _ h2))
  have e1 : aff y x = aff 1 x * aff y 0 := by rw [aff_mul]; simp
  convert h3 using 1
  simp only [b, hh, e1, mul_assoc, map_mul, Subgroup.coe_mul, map_inv]
  rw [TR.infGL_comm]
  simp
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

namespace UpperTheory.V.Br

section Aff
variable {R : Type} [CommRing R]

private theorem cm_aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem cm_aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem cm_scalar_comm (y : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) y = Matrix.GeneralLinearGroup.scalar (Fin 2) y * g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

end Aff

private theorem cm_ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

variable {F : Type} [Field F] [NumberField F]

private theorem cm_scal [MeasurableSpace (NA F)] (μ : Measure (NA F)) (D : Set (NA F)) (φ : GA F 2 → ℂ) {k : GA F 2} {z : ℂ}
    (hk : ∀ g, φ (g * k) = z * φ g) (g : GA F 2) (hg : cterm μ D φ g = 0) : cterm μ D φ (g * k) = 0 := by
  unfold cterm at hg ⊢
  simp only [← mul_assoc, hk]
  rw [integral_const_mul, hg, mul_zero]

variable [IsTotallyReal F]

private theorem cm_arch {ψ : GA F 2 → ℂ} {k : ℕ} (h : ∀ (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ),
    (∀ t v, (y t).val v = Real.exp (t * u v)) → ∀ g,
    HasDerivAt (fun t => ψ (TR.infGL F 2 (aff (y t) 0) * g)) ((k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ) * ψ g) 0)
    (y : (TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (g : GA F 2) (hg : ψ g = 0) :
    ψ (TR.infGL F 2 (aff y 0) * g) = 0 := by
  let u : TR.Rinf F := fun v => Real.log (y.val v)
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun v => Real.exp (t * u v), fun v => Real.exp (-(t * u v)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have h1 : z 1 = y := Units.ext (funext fun v => by simp [z, u, Real.exp_log (hy v)])
  have := cm_ode (f := fun t => ψ (TR.infGL F 2 (aff (z t) 0) * g)) (κ := (k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ)) fun t => by
    have h2 := h u z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, cm_aff_mul, ← hz]; simp
  rw [h1, h0, cm_aff_one, map_one, one_mul, hg, mul_zero] at this
  exact this

end UpperTheory.V.Br

theorem UpperTheory.V.Br.ctMoves :
    UpperTheory.V.Br.CtMoves := by
  intro F _ _ _ _ _ μ _ D hD k c ω hω φ hφ M hM
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  have hL := UpperTheory.eisenstein_continuous_left_action UpperTheory.eisenstein_smooth_continuous hB (UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock)
    UpperTheory.eisenstein_lie_algebra_action UpperTheory.eisenstein_central_lie_action
  obtain ⟨-, hN, hT⟩ := hB F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left
  refine ⟨fun x g hg => (hN x g).trans hg, fun a g hg => (hT a g).trans hg,
    fun y hy g hg => cm_arch (hL F μ D hD k c ω hω φ hφ) y hy g hg, fun z g hg => ?_, fun u hu g hg => ?_, fun θ h hh g hg => ?_⟩
  · rw [← cm_scalar_comm]
    exact cm_scal μ D φ.1 (fun g => by rw [cm_scalar_comm, hφ.cent]) g hg
  · exact cm_scal μ D φ.1 (z := 1) (fun g => by rw [one_mul]; exact congrFun (congrArg Subtype.val (hM u hu)) g) g hg
  · exact cm_scal μ D φ.1 (rotEig F φ _ hφ.wt θ h hh) g hg
end
end

section

open CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Br.minNew :
    UpperTheory.V.Br.MinNew := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hN hk χ g
    by_cases hnew : ∀ (M' : ℕ), M' ∣ N → M' ≠ N →
        ∀ (g' : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M')) ↑k)
          (χ' : DirichletCharacter ℂ M'), HasChar k χ' ⇑g' →
          (∀ᶠ (p : ℕ) in Filter.cofinite, Nat.Prime p → IsEigAt k χ' (⇑g') p (coef (⇑g.f) p)) → g' = 0
    · refine ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g.f, χ, g.char, g.one,
        fun p hp _ => g.eig p hp, hnew⟩, hN, g, rfl, Filter.Eventually.of_forall fun _ _ => rfl⟩
    · push_neg at hnew
      obtain ⟨M', hdvd, hne, g', χ', hc, hev, hg0⟩ := hnew
      have hM0 : M' ≠ 0 := by
        rintro rfl
        exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hdvd)
      haveI : NeZero M' := ⟨hM0⟩
      have hlt : M' < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hne
      obtain ⟨g'', hg''⟩ := UpperTheory.V.Br.eigEx M' k hk χ' g' hc hg0 (coef (⇑g.f))
      obtain ⟨f, hf, h, hhf, hha⟩ := ih M' hlt k hk χ' g''
      refine ⟨f, hf, h, hhf, ?_⟩
      filter_upwards [hha, hev] with p h1 h2 hp
      rw [h1 hp, hg'' p hp (h2 hp)]
      rfl
end
