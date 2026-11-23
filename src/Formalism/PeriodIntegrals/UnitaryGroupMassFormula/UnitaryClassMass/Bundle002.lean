module

public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle001

@[expose] public section

section

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Ad

open Classical

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {a b : Af F} (h : ∀ w, a w = b w) : a = b := Subtype.ext (funext h)

theorem af_mul_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem af_add_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem af_sub_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem af_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : Af F) w = 1 := rfl
theorem af_alg_apply (c : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) c) w = algebraMap F (w.adicCompletion F) c := rfl

variable (v : HeightOneSpectrum (𝓞 F))

def sgl (x : Fv F v) : Af F :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x

theorem sgl_apply (x : Fv F v) (w : HeightOneSpectrum (𝓞 F)) : sgl v x w = Pi.single v x w := rfl

theorem sgl_mul (x y : Fv F v) : sgl v (x * y) = sgl v x * sgl v y := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_add (x y : Fv F v) : sgl v (x + y) = sgl v x + sgl v y := af_ext fun w => by
  rw [af_add_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, add_zero]

theorem sgl_smul (c : F) (x : Fv F v) : c • sgl v x = sgl v (c • x) := af_ext fun w => by
  rw [Algebra.smul_def, Algebra.smul_def, af_mul_apply, af_alg_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_int {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : sgl v x ∈ intAf F := by
  intro w
  show sgl v x w ∈ w.adicCompletionIntegers F
  rw [sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same]; exact hx
  · rw [Pi.single_eq_of_ne hw]; exact zero_mem _

theorem sgl_one_mul (a : Af F) : sgl v 1 * a = sgl v (a v) := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, zero_mul]

def ivL : Fv F v →ₗ[F] Af F where
  toFun := sgl v
  map_add' := sgl_add v
  map_smul' c x := (sgl_smul v c x).symm

def evT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  (⟨fun w => if w ∈ T then (1 : w.adicCompletion F) else 0,
    Filter.Eventually.of_forall fun w => by
      show (if w ∈ T then (1 : w.adicCompletion F) else 0) ∈ w.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F])

theorem evT_apply (T : Set (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evT T w = if w ∈ T then 1 else 0 := rfl

theorem evT_int (T : Set (HeightOneSpectrum (𝓞 F))) : evT T ∈ intAf F := by
  intro w
  show evT T w ∈ w.adicCompletionIntegers F
  rw [evT_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem evT_eq_sum (T : Finset (HeightOneSpectrum (𝓞 F))) : evT (T : Set _) = ∑ w ∈ T, sgl w 1 := by
  apply af_ext
  intro w

  rw [evT_apply, show (∑ w' ∈ T, sgl w' 1) w = evalV F w (∑ w' ∈ T, sgl w' 1) from rfl, map_sum]
  simp only [show ∀ w', evalV F w (sgl w' 1) = Pi.single w' 1 w from fun _ => rfl]
  by_cases hw : w ∈ T
  · rw [if_pos (by exact_mod_cast hw), Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hw h
  · rw [if_neg (by exact_mod_cast hw)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have : w ≠ b := fun h => hw (h ▸ hb)
    simp [Pi.single_apply, this]

theorem one_sub_evT_inv_int (T : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F)
    (ht : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → t ∉ w.asIdeal) :
    (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  intro w
  show ((1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) w ∈ w.adicCompletionIntegers F
  rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
  split_ifs with hw
  · rw [sub_self, zero_mul]; exact zero_mem _
  · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : algebraMap F (w.adicCompletion F) ((algebraMap (𝓞 F) F t)⁻¹) =
        (((algebraMap (𝓞 F) F t)⁻¹ : F) : w.adicCompletion F) := rfl
    rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 (ht w hw), inv_one]

end Ad

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

def Psi : Af F ⊗[F] E →ₐ[F] E ⊗[F] Fv F v :=
  (Algebra.TensorProduct.comm F (Fv F v) E).toAlgHom.comp
    (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))

theorem Psi_tmul (a : Af F) (e : E) : Psi (E := E) v (a ⊗ₜ[F] e) = e ⊗ₜ[F] a v := by
  simp [Psi]; rfl

def Phi : E ⊗[F] Fv F v →ₗ[F] Af F ⊗[F] E :=
  (TensorProduct.map (ivL v) LinearMap.id) ∘ₗ (TensorProduct.comm F E (Fv F v)).toLinearMap

theorem Phi_tmul (e : E) (x : Fv F v) : Phi v (e ⊗ₜ[F] x) = sgl v x ⊗ₜ[F] e := by
  simp [Phi]; rfl

theorem Phi_Psi (r : Af F ⊗[F] E) : Phi v (Psi v r) = (sgl v 1 ⊗ₜ[F] (1 : E)) * r := by
  induction r using TensorProduct.inductionOn with
  | tmul a e =>
    rw [Psi_tmul, Phi_tmul, Algebra.TensorProduct.tmul_mul_tmul, sgl_one_mul, one_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, mul_add]

theorem Phi_mul (x y : E ⊗[F] Fv F v) : Phi v (x * y) = Phi v x * Phi v y := by
  induction x using TensorProduct.inductionOn with
  | tmul e a =>
    induction y using TensorProduct.inductionOn with
    | tmul e' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Phi_tmul, Phi_tmul, Phi_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

theorem Phi_inclE (e : E) : Phi v (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e) = sgl v 1 ⊗ₜ[F] e := by
  show Phi v (e ⊗ₜ[F] (1 : Fv F v)) = _
  rw [Phi_tmul]

theorem Phi_int {s : E ⊗[F] Fv F v}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F v) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring) :
    Phi v s ∈ Oh F E := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v (one_mem _)) o.isIntegral_coe
    · rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v hy) isIntegral_one
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show (1 : E ⊗[F] Fv F v) = (1 : E) ⊗ₜ[F] (1 : Fv F v) from rfl, Phi_tmul]
    exact tmul_mem_Oh (sgl_int v (one_mem _)) isIntegral_one
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1
  | mul x y _ _ h1 h2 => rw [Phi_mul]; exact Oh_mul h1 h2

end Tens

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Fam

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n]
  [DecidableEq n]

theorem fam_mul (e : ι → R) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (A B : ι → Matrix n n R) :
    (∑ i, e i • A i) * (∑ j, e j • B j) = ∑ i, e i • (A i * B i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i, ite_smul, zero_smul]
  simp

theorem fam_one (e : ι → R) (hs : ∑ i, e i = 1) (X : Matrix n n R) : ∑ i, e i • X = X := by
  rw [← Finset.sum_smul, hs, one_smul]

theorem cT_fam (s : R →+* R) (e : ι → R) (A : ι → Matrix n n R) :
    cT s (∑ i, e i • A i) = ∑ i, s (e i) • cT s (A i) := by
  ext a c

  simp [cT, Matrix.sum_apply, map_sum, Matrix.smul_apply, map_mul]

end Fam

section Patch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]


variable (F E) in
abbrev finE : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

def incM (U : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  (U : Matrix (Fin M) (Fin M) E).map (inclR (AF F))

theorem incM_mul_inv (U : GL (Fin M) E) : incM (F := F) U * incM (F := F) U⁻¹ = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_inv_mul (U : GL (Fin M) E) : incM (F := F) U⁻¹ * incM (F := F) U = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_unitary (U : GL (Fin M) E) (hU : U ∈ UJ (σ : E →+* E) J) :
    cT (sigR (AF F) σ) (incM (F := F) U) * JR (AF F) J * incM (F := F) U = JR (AF F) J := by
  have := PI.UnitaryGroupMassFormula.UJClassFin.bc_mem (F := F) σ J U hU
  exact this

def patchGL (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (γ : ι → GL (Fin M) E) : GL (Fin M) (AF F ⊗[F] E) where
  val := ∑ i, e i • incM (γ i)
  inv := ∑ i, e i • incM (γ i)⁻¹
  val_inv := by
    rw [fam_mul e he]
    simp_rw [incM_mul_inv]
    exact fam_one e hs 1
  inv_val := by
    rw [fam_mul e he]
    simp_rw [incM_inv_mul]
    exact fam_one e hs 1

theorem patchGL_mem (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : patchGL e he hs γ ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) (∑ i, e i • incM (γ i)) * JR (AF F) J * (∑ i, e i • incM (γ i)) = JR (AF F) J
  rw [cT_fam]
  simp_rw [hσe]
  conv_lhs => rw [← fam_one e hs (JR (AF F) J)]
  rw [fam_mul e he, fam_mul e he]
  simp_rw [incM_unitary σ J _ (hγ _)]
  exact fam_one e hs _

def patchHA (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (⟨patchGL e he hs γ, patchGL_mem σ J e he hs hσe γ hγ⟩ : HR (AF F) σ J)

theorem finE_inclR (x : E) : finE F E (inclR (AF F) x) = inclR (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem finMat_patch_inv (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) :
    finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      ∑ i, finE F E (e i) • ((γ i)⁻¹ : GL (Fin M) E).val.map (inclR (Af F)) := by
  have h0 : finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      (∑ i, e i • incM (F := F) (γ i)⁻¹).map (finE F E) := rfl
  rw [h0]
  ext a c

  simp [Matrix.map_apply, Matrix.sum_apply, incM, map_sum, map_mul, finE_inclR]

theorem patch_mulVec (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) (x : Fin M → E) :
    (finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x) =
      ∑ i, finE F E (e i) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (((γ i)⁻¹ : GL (Fin M) E).val.mulVec x) := by
  rw [finMat_patch_inv, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mulVec, PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc]

end Patch

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem Oh_smul_latHat (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    {z : Af F ⊗[F] E} (hz : z ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : z • y ∈ latHat F E L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * c, PI.UnitaryGroupMassFormula.UJClassFin.intAf_mul ha hc, t • x, hL t ht x hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y w _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add z w _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg z _ h1 => rw [neg_smul]; exact neg_mem h1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem latHat_split (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    (f : ι → Af F ⊗[F] E) (hf : ∀ i j, f i * f j = if i = j then f i else 0)
    (hO : ∀ i, f i ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) (y : ι → Fin M → Af F ⊗[F] E) :
    ∑ i, f i • y i ∈ latHat F E L ↔ ∀ i, f i • y i ∈ latHat F E L := by
  constructor
  · intro h j
    have h1 := Oh_smul_latHat L hL (hO j) h
    have e : f j • ∑ i, f i • y i = f j • y j := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hf j, ite_smul, zero_smul]
      simp
    rwa [e] at h1
  · intro h
    exact AddSubgroup.sum_mem _ (fun i _ => h i)

end Split

theorem crd_int_smul {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ} (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ crdOf b L0, e • x ∈ crdOf b L0 := by
  intro e he x hx
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    simp [smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx

theorem equivFun_toLin {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (A : Matrix (Fin M) (Fin M) E) (v : V) :
    b.equivFun (Matrix.toLin b b A v) = A.mulVec (b.equivFun v) := by
  rw [Matrix.toLin_apply, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem equivFun_linOf_symm {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (v : V) :
    b.equivFun ((linOf b U).symm v) = ((U⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  rw [← equivFun_toLin]
  rfl

end PI.UnitaryGroupMassFormula.UJClassMass

end
end
