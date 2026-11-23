module

public import Development.WeilBound.ThetaLifts.SmallCones.Bundle005
import Development.WeilBound.ThetaLifts.SmallCones.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.ThetaLifts.CTKernel
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003

@[expose] public section

section

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem units_sum {K : Type} [Field K] {a : K → ℂ} (ha : Summable a) : ∑' ξ : Kˣ, a ξ = ∑' x, a x - a 0 := by
  have h1 := ha.tsum_subtype_add_tsum_subtype_compl {0}
  rw [tsum_singleton] at h1
  rw [← h1, add_sub_cancel_left]
  exact (unitsEquivNeZero (G₀ := K)).tsum_eq fun x => a x.1

theorem orbit_sum {Γ I : Type} [Group Γ] [MulAction Γ I] (hfree : ∀ (ξ η : Γ) (x : I), ξ • x = η • x → ξ = η) {f : I → ℂ}
    (hf : Summable f) : ∑' x, f x = ∑' q : MulAction.orbitRel.Quotient Γ I, ∑' ξ : Γ, f (ξ • q.out) := by
  have hb : Function.Bijective fun y : MulAction.orbitRel.Quotient Γ I × Γ => y.2 • y.1.out := by
    constructor
    · rintro ⟨q, ξ⟩ ⟨q', η⟩ h
      dsimp only at h
      have : q = q' := by
        rw [← q.out_eq, ← q'.out_eq]
        exact Quotient.sound ⟨ξ⁻¹ * η, by dsimp only; rw [mul_smul, ← h, inv_smul_smul]⟩
      subst this
      rw [hfree _ _ _ h]
    · intro x
      obtain ⟨ξ, hξ⟩ : (Quotient.mk (MulAction.orbitRel Γ I) x).out ∈ MulAction.orbit Γ x := Quotient.mk_out (s := MulAction.orbitRel Γ I) x
      exact ⟨(Quotient.mk _ x, ξ⁻¹), by dsimp only at hξ ⊢; rw [← hξ, inv_smul_smul]⟩
  rw [← (Equiv.ofBijective _ hb).tsum_eq]
  exact ((Equiv.ofBijective _ hb).summable_iff.2 hf).tsum_prod

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem form_smul (J : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin n → E) : form σ J (c • x) (c • x) = c * σ c * form σ J x x := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance isoAct : MulAction Eˣ (IsoV σ X) where
  smul ξ x := ⟨(ξ : E) • x.1, smul_ne_zero ξ.ne_zero x.2.1, by rw [form_smul, x.2.2, mul_zero]⟩
  one_smul x := Subtype.ext (one_smul E x.1)
  mul_smul a b x := Subtype.ext (mul_smul (a : E) (b : E) x.1)

theorem isoAct_val (ξ : Eˣ) (x : IsoV σ X) : (ξ • x).1 = (ξ : E) • x.1 := rfl

theorem isoAct_free (ξ η : Eˣ) (x : IsoV σ X) (h : ξ • x = η • x) : ξ = η :=
  Units.ext (smul_left_injective E x.2.1 (congrArg Subtype.val h))

def conjE (hσ : IsCMExt F E σ) : Eˣ ≃ Eˣ where
  toFun := Units.map (σ : E →* E)
  invFun := Units.map (σ : E →* E)
  left_inv x := Units.ext (cm_conj_conj hσ x.1)
  right_inv x := Units.ext (cm_conj_conj hσ x.1)

abbrev idl (ξ : Eˣ) : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom ξ

theorem incV_smul (c : E) (x : Fin n → E) : incV F (c • x) = inclR (F := F) (AF F) c • incV F x := by
  funext i
  simp [incV]

theorem incM_smul (c : E) (x : Matrix (Fin n) (Fin d) E) : incM F (c • x) = inclR (F := F) (AF F) c • incM F x := by
  ext i j
  simp [incM]

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.mult (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic)
    (hp : IsPair B M χX χW om r s r' s') (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {γ} (hγ : Moves (σ := σ) (X := X) H γ) (y g) (x : IsoV σ X) (ξ η : Eˣ) (hη : ι (idl η) = idl ξ⁻¹) (hν : w (idl η) = 1) :
    thv B M om e (u 1) Φ y (γ (ξ • x) * g) = thetaSum F (e (M.co.rho B.ψ (u (idl η)) (om (γ x * g, y) Φ))) := by
  obtain ⟨-, -, -, -, ⟨lev, -, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH
  have hl := hlev (idl ξ⁻¹) 1
  have hr := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).2.1 ξ⁻¹ 1 (one_mem _) _ hl
  set p := lev (idl ξ⁻¹, 1)
  have h1 : mat (p * γ x) *ᵥ incV F (ξ • x).1 = incV F H.x := by
    rw [mat_mul', ← Matrix.mulVec_mulVec, isoAct_val, incV_smul, Matrix.mulVec_smul, (hγ x).2, Matrix.mulVec_smul, hl.1, smul_smul]
    simp [← map_mul]
  have h2 := h.rat hD hTB hp hp₀ hH hs hΦ y (δ := γ (ξ • x) * (p * γ x)⁻¹)
    (mul_mem (hγ _).1 (inv_mem (mul_mem hr (hγ x).1)))
    (by rw [mat_mul', ← Matrix.mulVec_mulVec, mat_inv_mulVec _ h1, (hγ _).2]) (p * γ x * g)
  rw [show γ (ξ • x) * (p * γ x)⁻¹ * (p * γ x * g) = γ (ξ • x) * g by group] at h2
  have h3 := h.theta (l := idl η) (by rwa [hη]) (levi_one (W₁ := W₁) H') (pair_pres hp (γ x * g, y) hΦ)
  rw [hη, hν, GlobalTheory.Doubling.absE_inclR] at h3
  rw [h2]
  simpa [thv, om_mul, mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk] using h3

end

end PositivityTheory.ThKCT

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.fin [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    ∫⁻ k, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ∂μK < ⊤ := by
  set J : Fin m → (AE F E)ˣ × UA σ X₁.J → ℂ := fun i x =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) (Ψ i))) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) with hJ
  have hJi : ∀ i, Integrable (J i) (μ.prod (M₀.μ.restrict M₀.dom)) := fun i => h.int _ (hΨ i) h₁
  have key : ∀ k : K, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ≤
      ∑ i, ‖c i k‖ₑ * ∫⁻ x, ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) := fun k => by
    have e1 : ∀ l g, theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
        ∑ i, c i k * J i (l, g) := fun l g => by
      simp only [hd, h.val_sum _ hΨ, hJ, Finset.sum_mul, mul_assoc]
    simp only [e1]
    have hi : Integrable (fun x => ∑ i, c i k * J i x) (μ.prod (M₀.μ.restrict M₀.dom)) :=
      integrable_finsetSum _ fun i _ => (hJi i).const_mul _
    rw [← lintegral_prod (fun x => ‖∑ i, c i k * J i x‖ₑ) hi.1.enorm]
    calc _ ≤ ∫⁻ x, ∑ i, ‖c i k‖ₑ * ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) :=
          lintegral_mono fun x => (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (enorm_mul _ _).le)
      _ = _ := by
          rw [lintegral_finsetSum' _ fun i _ => (hJi i).1.enorm.const_mul _]
          exact Finset.sum_congr rfl fun i _ => lintegral_const_mul'' _ (hJi i).1.enorm
  refine (lintegral_mono key).trans_lt ?_
  rw [lintegral_finsetSum' _ fun i _ => (hc i).1.enorm.mul_const _]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_mul_const'' _ (hc i).1.enorm]
  exact ENNReal.mul_lt_top (hc i).2 (hJi i).2

theorem LineOK.unf [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (ι : (AE F E)ˣ → (AE F E)ˣ)
    (hι : ∀ G : (AE F E)ˣ → ℝ≥0∞, ∫⁻ l, G (ι l) ∂μ = ∫⁻ l, G l ∂μ) (hι' : ∀ G : (AE F E)ˣ → ℂ, ∫ l, G (ι l) ∂μ = ∫ l, G l ∂μ)
    (lev : (AE F E)ˣ × UA σ X₁.J → UA σ X.J) (f : UA σ X.J → ℂ)
    (hf : ∀ l g (k : K), f (lev (ι l, g) * k.1) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g 1 * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) :
    ∫⁻ k, ∫⁻ l, (∫⁻ g in M₀.dom, ‖f (lev (l, g) * k.1)‖ₑ ∂M₀.μ) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ ∂μK < ⊤ ∧
    ∫ k, ∫ l, (∫ g in M₀.dom, f (lev (l, g) * k.1) ∂M₀.μ) * (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) ∂μ ∂μK =
      coneI B M om M₀ om₀ e K μK μ u ν z Φ 1 := by
  constructor
  · convert h.fin μK hΨ hc hd 1 using 3 with k
    rw [← hι]
    congr 1
    funext l
    rw [← lintegral_mul_const' _ _ (by simp)]
    congr 1
    funext g
    have he : ENNReal.ofReal ((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ))) =
        ‖(((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    rw [he, ← eNorm_mul, hf]
  · unfold coneI
    congr 1
    funext k
    rw [← hι']
    congr 1
    funext l
    rw [← integral_mul_const]
    simp only [hf, Model.I, integral_mul_const, mul_assoc]

end Core

end PositivityTheory.ThKCT

end
end
