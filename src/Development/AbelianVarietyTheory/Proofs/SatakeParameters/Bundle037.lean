module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section


theorem _root_.GlobalTheory.T.ind_etale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  first | (exact @GlobalTheory.IndEtaleComp.isIndEtale_comp) | (exact GlobalTheory.IndEtaleComp.isIndEtale_comp) | (intros; apply GlobalTheory.IndEtaleComp.isIndEtale_comp <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne TensorProduct

namespace GlobalTheory.WeilDeligne.TwistInj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem apply_eq_det_smul (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ) :
    f v = LinearMap.det f • v := by
  have hd : LinearMap.det f = f (Pi.single 0 1) 0 := by
    conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
    rw [LinearMap.det_toLin', Matrix.det_fin_one, LinearMap.toMatrix'_apply]
  have hv : v = v 0 • (Pi.single 0 1 : Fin 1 → ℂ) := by
    funext i; fin_cases i; simp
  funext i; fin_cases i
  rw [hv, map_smul, hd]
  simp [mul_comm]

def chr (c : WDRep h (Fin 1 → ℂ)) : Weil h →* ℂˣ :=
  (Units.map (LinearMap.det : Module.End ℂ (Fin 1 → ℂ) →* ℂ)).comp c.ρ.asGroupHom

theorem coe_chr (c : WDRep h (Fin 1 → ℂ)) (σ : Weil h) :
    (chr c σ : ℂ) = LinearMap.det (c.ρ σ) := by
  simp [chr, Representation.asGroupHom_apply]

theorem isSmooth_chr (c : WDRep h (Fin 1 → ℂ)) : IsSmooth (chr c) :=
  c.smooth.of_le fun σ hσ => Units.ext (by rw [coe_chr, hσ, map_one]; rfl)

theorem N_eq_zero (c : WDRep h (Fin 1 → ℂ)) : c.N = 0 := by
  have hz : LinearMap.det (0 : Module.End ℂ (Fin 1 → ℂ)) = 0 := by
    have := congrFun (apply_eq_det_smul 0 (fun _ => 1)) 0
    simpa using this.symm
  obtain ⟨k, hk⟩ := c.nilpotent
  have h0 : LinearMap.det c.N = 0 := by
    have : LinearMap.det c.N ^ k = 0 := by rw [← map_pow, hk, hz]
    exact pow_eq_zero_iff'.mp this |>.1
  refine LinearMap.ext fun v => ?_
  rw [apply_eq_det_smul, h0, zero_smul]
  rfl

theorem tensor_iso_twist {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (c : WDRep h (Fin 1 → ℂ)) :
    (a.tensor c).Iso (a.twist (chr c) (isSmooth_chr c)) := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.funUnique_apply,
        TensorProduct.rid_tmul, WDRep.twist_ρ, LinearMap.smul_apply, map_smul, coe_chr]
      rw [apply_eq_det_smul (c.ρ σ) y, smul_smul]
      simp [Function.eval, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [N_eq_zero c, Function.eval, WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_of_twist {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {a : WDRep h V} {b : WDRep h V'} (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (hab : (a.twist χ hχ).Iso (b.twist χ hχ)) : a.Iso b := by
  obtain ⟨e, h1, h2⟩ := hab
  refine ⟨e, fun σ v => ?_, h2⟩
  have := h1 σ v
  simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul] at this
  exact smul_right_injective V' (Units.ne_zero (χ σ)) this

end GlobalTheory.WeilDeligne.TwistInj


open GlobalTheory.WeilDeligne.TwistInj in
theorem GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c hc hab
  induction a using WD.ind with
  | hP n a =>
  induction b using WD.ind with
  | hP m b =>
  induction c using WD.ind with
  | hP k c =>
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hc
  subst hc
  rw [WD.lpChar_mk, WD.lpChar_mk, WD.mk_eq_mk] at hab
  exact WD.sound (TwistInj.iso_of_twist (TwistInj.chr c) (TwistInj.isSmooth_chr c)
    (((TwistInj.tensor_iso_twist a c).symm.trans hab).trans (TwistInj.tensor_iso_twist b c)))
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem absSpace_eq_bot_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    absSpace f r = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun α hα => ?_)
  by_contra hne
  have hev : f.HasEigenvalue α := Module.End.hasEigenvalue_iff.mpr fun h => hne (h ▸ le_refl _)
  have hroot : (minpoly ℂ f).IsRoot α := Module.End.hasEigenvalue_iff_isRoot.mp hev
  have hc : α ∈ f.charpoly.roots := by
    rw [mem_roots (LinearMap.charpoly_monic f).ne_zero, ← Polynomial.dvd_iff_isRoot]
    exact (Polynomial.dvd_iff_isRoot.mpr hroot).trans (LinearMap.minpoly_dvd_charpoly f)
  exact hr (hα ▸ hf α hc)

theorem absSpace_one_eq_top_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by
  rw [eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : ‖α‖ = 1
  · exact le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = 1) => f.eigenspace β) α hα le_rfl
  · have := absSpace_eq_bot_of_norm_charpoly_roots hf hα
    rw [eq_bot_iff] at this
    refine le_trans ?_ (bot_le : (⊥ : Submodule ℂ V) ≤ absSpace f 1)
    exact le_trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = ‖α‖) => f.eigenspace β) α rfl le_rfl) this

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  intro E Ω _ _ _ _ _ A w h a _ heig
  induction a using WD.ind with
  | hP n a =>
  rw [WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := by
    intro α hα; exact heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hne : ∀ s : ℝ, s ≠ 0 → ((normV w : ℕ) : ℝ) ^ s ≠ 1 := by
    intro s hs h1
    rw [← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
    exact hs h1
  refine ⟨eq_top_iff.mpr ?_, fun i => ?_⟩
  · rw [← absSpace_one_eq_top_of_norm_charpoly_roots (a.semisimple φ) hroots]
    refine le_iSup_of_le (0 : ℤ) ?_
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, Nat.cast_zero, neg_zero]
      exact Set.bijOn_id _
    · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
      rw [absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith)),
        absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith))]
      simp only [Submodule.bot_coe]
      exact ⟨fun v hv => by rw [Set.mem_singleton_iff.mp hv, map_zero]; rfl,
        fun v hv v' hv' _ => by rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp hv'],
        fun v hv => ⟨0, rfl, by rw [Set.mem_singleton_iff.mp hv, map_zero]⟩⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']

namespace WDRep

theorem iso_sum_tensor (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.sum b).tensor c).Iso ((a.tensor c).sum (b.tensor c)) := by
  refine ⟨TensorProduct.prodLeft ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_tw_tensor (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    ((a.tw s).tensor c).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_left], fun _ => rfl⟩

theorem iso_tensor_tw (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    (a.tensor (c.tw s)).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_right], fun _ => rfl⟩

theorem iso_tensor_assoc (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.tensor b).tensor c).Iso (a.tensor (b.tensor c)) := by
  refine ⟨TensorProduct.assoc ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [tmul_add, add_tmul, add_assoc]
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]

theorem iso_zero_tensor (a : WDRep h V) (c : WDRep h V') [Subsingleton V] (b : WDRep h V'') [Subsingleton V''] :
    (a.tensor c).Iso b := by
  haveI : Subsingleton (V ⊗[ℂ] V') := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : V ⊗[ℂ] V', z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [key x, key y]
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem ρ_eq_one_of_line (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have hv1 : c.ρ (frob h) v = v := by simpa using hv.apply_eq_smul
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv.2).mp hd
  have hF : c.ρ (frob h) = 1 := LinearMap.ext fun u => by
    obtain ⟨t, rfl⟩ := hspan u
    simp [hv1]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1 := fun n => by
    have h1 : c.ρ.toHomUnits (frob h) = 1 := Units.ext hF
    have h2 : c.ρ.toHomUnits (frob h ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
    exact congrArg Units.val h2
  rw [hτ, map_mul, hz, hu.2 τ, one_mul]

theorem iso_tensor_line (a : WDRep h V) (c : WDRep h V') (hN : c.N = 0) (hd : finrank ℂ V' = 1)
    (hρ : ∀ σ, c.ρ σ = 1) : (a.tensor c).Iso a := by
  let f : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)
  refine ⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end WDRep

namespace WD

theorem lpChar_laws (a b c : WD h) (s : ℝ) :
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  refine ⟨?_, ?_, ?_, ?_, ?_, fun hu hd he => ?_⟩
  · simp only [lpSum_mk, lpChar_mk]
    exact sound (a.iso_sum_tensor b c)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tw_tensor c s)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tensor_tw c s)
  · simp only [lpChar_mk]
    exact sound (a.iso_tensor_assoc b c)
  · simp only [lpZero, lpChar_mk]
    exact sound (WDRep.iso_zero_tensor _ c _)
  · rw [unr_mk] at hu
    rw [lpDim_mk] at hd
    rw [frobEig_mk] at he
    have hroot : (c.ρ (frob h)).charpoly.IsRoot 1 := by
      have h1 : (1 : ℂ) ∈ (c.ρ (frob h)).charpoly.roots := by rw [he]; simp
      exact (Polynomial.mem_roots'.mp h1).2
    rw [lpChar_mk]
    exact sound (a.iso_tensor_line c hu.1 hd (c.ρ_eq_one_of_line hu hd hroot))

end WD

theorem lpChar_laws_closed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ),
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) :=
  fun _ _ _ _ _ _ _ _ _ _ a b c s => WD.lpChar_laws a b c s

end GlobalTheory.WeilDeligne
end
end

section

noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem exists_aic_local_subring (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] (φ : k →+* K) :
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  obtain ⟨D, m₀, hD, hm₀, hres, hint⟩ := GlobalTheory.T.exists_polynomialSubring_maximal_integral k K φ
  obtain ⟨R, 𝔪, hR, h𝔪, hres', hfr, hic⟩ := GlobalTheory.T.integralClosure_maximal_residue_of_algClosed k K φ D m₀ hD hm₀ hres hint
  exact GlobalTheory.T.exists_local_subring_monic_roots_residue k K φ R 𝔪 hR h𝔪 hres' hfr hic

section Eqv
variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_trans {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_of_eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := by
  intro n
  have h : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun x y hxy => (hfg n).1 (by rw [h, h, hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hfg n).2 (pull R f F n y)
  exact ⟨x, (hf n).1 (by rw [← h, hx])⟩

variable {X Y W S : Scheme.{0}} (p : X ⟶ S) (d : Y ⟶ S) (g : W ⟶ Y)

theorem fst_comp_eq : pullback.fst p (g ≫ d) =
    (pullbackLeftPullbackSndIso p d g).inv ≫ pullback.fst (pullback.snd p d) g ≫ pullback.fst p d := by
  rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_fst]

theorem eqv_fst_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p d)) F) : Eqv R (sch.map (pullback.fst p (g ≫ d))) F := by
  rw [fst_comp_eq, Functor.map_comp, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) (eqv_trans F h1 h2)

theorem eqv_fst_of_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p (g ≫ d))) F) : Eqv R (sch.map (pullback.fst p d)) F := by
  refine eqv_of_eqv_comp F h1 ?_
  have : pullback.fst (pullback.snd p d) g ≫ pullback.fst p d =
      (pullbackLeftPullbackSndIso p d g).hom ≫ pullback.fst p (g ≫ d) := by
    rw [pullbackLeftPullbackSndIso_hom_fst]
  rw [← Functor.map_comp, this, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) h2

end Eqv

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem eqv_fieldChange (hE2 : E2) (hE3 : E3) (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K]
    [IsAlgClosed K] (φ : k →+* K) (hq : IsUnit (q : k)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) (tw q i) := by
  obtain ⟨T, hφT, ⟨hloc, hT, hres⟩, hfr⟩ := exists_aic_local_subring k K φ
  let α : k →+* T := φ.codRestrict T (fun c => hφT ⟨c, rfl⟩)
  have hqT : IsUnit (q : T) := by simpa using hq.map α
  let a := Spec.map (CommRingCat.ofHom α)

  have hb : Function.Bijective ((IsLocalRing.residue T).comp α) := by
    refine ⟨(IsLocalRing.residue T).comp α |>.injective, fun y => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, h, hc⟩ := hres t
    refine ⟨c, ?_⟩
    change IsLocalRing.residue T (α c) = IsLocalRing.residue T t
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have e : α c - t = -(t - ⟨φ c, h⟩) := by rw [neg_sub]; rfl
    rw [e]
    exact (IsLocalRing.maximalIdeal T).neg_mem hc
  haveI : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue T))
  have hra : r ≫ a = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) := (spec_comp _ _).symm
  have hsp : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a) r)) (tw q i) :=
    eqv_spInc hE2 hT q hqT (pullback.snd p a) i
  have hXT : Eqv (ZMod q) (sch.map (pullback.fst p a)) (tw q i) := by
    refine eqv_fst_of_comp _ p a r hsp ?_
    rw [hra]
    exact eqv_iso _ _

  let e := IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K
  have hφ : φ = (e.toRingEquiv.toRingHom).comp ((algebraMap T (FractionRing T)).comp α) := by
    ext c
    simp only [RingHom.comp_apply]
    rw [show e.toRingEquiv.toRingHom (algebraMap T (FractionRing T) (α c)) = e (algebraMap T (FractionRing T) (α c)) from rfl,
      AlgEquiv.commutes]
    rfl
  haveI : IsIso (CommRingCat.ofHom (e.toRingEquiv.toRingHom)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have hgen : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a)
      (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i) :=
    eqv_genInc hE3 hT q hqT (pullback.snd p a) i
  rw [hφ, spec_comp, spec_comp]
  refine eqv_fst_comp _ p _ _ (eqv_iso _ _) (eqv_fst_comp _ p a _ hgen hXT)

end GlobalTheory.GenusTwoPureComparison.Cmp
end
end
