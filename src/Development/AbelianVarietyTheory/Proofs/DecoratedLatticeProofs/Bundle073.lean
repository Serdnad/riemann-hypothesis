module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem val_unif' {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem sqrt_pow (q : ℝ) (hq : 0 < q) (v : ℤ) (N : ℕ) :
    (q ^ (-v)) ^ ((N : ℝ) / 2) = (Real.sqrt q) ^ (-v * N) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

theorem char_scalar (hok : cst.Ok) (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) (a : X.E) (u : kˣ)
    (hu : (u : k) = ι a) (N : ℕ) :
    ((W.η (s + 1) * W.δ) u : ℂ) * ((nabs k u ^ ((N : ℝ) / 2) : ℝ) : ℂ) =
      W.sg ^ (LocE.vP P.1 (qOf P.1) a * N) *
        σ₀ (muAt Ch sel mu cst s P a * cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) a) * N)) := by
  have hC := hA.compl
  have hU := W.unif
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := ComplRes.q_ne_zero hC
  have hvalu := val_unif' hU
  have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z)) := by
    obtain ⟨z, hz⟩ := NormalForm.exists_valuation_eq_zpow hvalu u
    refine ⟨z, ?_⟩
    have hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1 := by
      rw [map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]
      exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)
    exact (ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1
  have hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
    unfold LocE.vP; exact Classical.epsilon_spec hex
  set v := LocE.vP P.1 (qOf P.1) a with hvdef
  set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef
  have hbI : IntAt P.1 b := by
    by_contra h; rw [reduction_eq_zero_of_not_integral P.1 h] at hspec; exact not_isUnit_zero hspec
  have hbv : valuation k (ι b) = 1 := (ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec
  have hb0 : ι b ≠ 0 := by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv
  set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef
  have hu_eq : u = W.ϖ ^ v * ub := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef,
      mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]
  have hη : W.η (s + 1) ub = 1 := W.unr (s + 1) ub hbv
  have hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := hA.del b ub hbI hspec rfl
  have hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P) := hA.mu s (by rw [hA.steps]; omega)
  have hnU : nabs k ub = 1 := nabs_eq_one_of_valuation_eq_one hbv
  obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU
  have hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹ := by
    rw [nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]
  have hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v) := by
    rw [hu_eq]
    unfold nabs
    rw [map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]
    have h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹ := hnϖ
    have h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1 := hnU
    rw [h1, h2, mul_one, _root_.inv_zpow']
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := congrArg σ₀ (hok.sq_sq P)
    rw [map_pow, hA.sq, h0, zero_mul, map_natCast] at h2
    exact hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)
  have hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹ := by
    unfold muAt LocE.locChar
    rw [if_neg hA.nmem, ← hvdef, ← hbdef]
    congr 1
    unfold LocE.unitV
    rw [dite_eq_left hspec, dite_eq_left hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := by
    rw [hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη,
      Units.val_one, one_mul, hδ]
  have hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ) := by
    have : (qOf P.1 : ℕ) ≠ 0 := fun h => hq0 (by rw [h, Nat.cast_zero])
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [hchar, hn, sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]
  push_cast
  have hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1 := by
    rw [neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]
  linear_combination (σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ *
    (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)

end GlobalTheory.TwBridge.PsiRat

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

theorem toLoc_comp_rect {E k : Type} [Field E] [Field k] (ι : E →+* k) {A B C : Type} [Fintype B] [DecidableEq B]
    {a b c : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) (eC : C ≃ Fin c) (x : (Fin b → E) →ₗ[E] (Fin a → E))
    (y : (Fin c → E) →ₗ[E] (Fin b → E)) :
    toLoc ι eA eB x * toLoc ι eB eC y = toLoc ι eA eC (x ∘ₗ y) := by
  have h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : (Fin b → E) →ₗ[E] (Fin a → E)),
      toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι := by
    intro A B a b e e' z
    ext i j
    simp [toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ eA eB eC, Matrix.map_mul]

theorem muAt_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
    (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) :
    muAt Ch sel mu cst i P 1 = 1 := by
  unfold muAt LocE.locChar
  rw [PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by rw [PsiStep.reduction_one']; exact isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left h1]
  have : h1.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])
  rw [this, map_one, Units.val_one]

end GlobalTheory.TwBridge.PsiRat

namespace GlobalTheory.TwBridge


open PsiRat in
theorem psi_rat_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  obtain ⟨eg, hegO, hgv⟩ := hg
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hegE : eg = E' := Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)
  subst hegE
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') :=
    PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'
  have hprod : toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) :=
    toLoc_comp_rect ι E₁ E' E' _ _
  have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E) := by
    have h := RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')
    rw [RingHom.mapMatrix_apply] at h
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h,
      Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1) := by
    rw [Fintype.card_congr E₁, Fintype.card_fin]
  have hPhi1 := hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)
  have hsc := char_scalar Ch sel mu cst σ₀ P ι s W hok hA _ _ hdet (R.N (s + 1) + cOf R (s + 1))
  have hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by
    rw [← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]
    clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'
    unfold Chain.Psi GlobalTheory.SplitWeil.om
    have hn1 : nabs k (1 : kˣ) = 1 := by unfold nabs; rw [map_one, NNReal.coe_one]
    simp only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul]
    rfl
  rw [hL, hsc]
  unfold PsiAt omPhi Loc.om sgn
  simp only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]
  have h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ
      (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) =
        joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by
    ext v; rfl
  rw [h1]
  simp only [map_mul]
  ring

end GlobalTheory.TwBridge
end
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.MulCoord

variable (I : AutInst)

def vecHom (y : I.Ginf) : (Fin I.n → I.E) →+ (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun := vec I y
  map_zero' := by
    funext v
    have h0 : (fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0 := by funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0
    rw [h0, mulVec_zero, mulVec_zero]
  map_add' u w := by
    funext v
    have h : (fun i => I.φ v ((u + w) i)) = (fun i => I.φ v (u i)) + fun i => I.φ v (w i) := by
      funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((u + w) i)) =
      uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) + uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (w i))
    rw [h, mulVec_add, mulVec_add]

theorem vec_sum_zsmul {N : ℕ} (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    vec I y (∑ k, z k • e k) = ∑ k, z k • vec I y (e k) := by
  calc vec I y (∑ k, z k • e k) = vecHom I y (∑ k, z k • e k) := rfl
    _ = ∑ k, vecHom I y (z k • e k) := map_sum _ _ _
    _ = ∑ k, z k • vecHom I y (e k) := by simp only [map_zsmul]
    _ = _ := rfl

theorem vec_smul (y : I.Ginf) (a : I.E) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y (a • u) v = I.φ v a • vec I y u v := by
  have h : (fun i => I.φ v ((a • u) i)) = I.φ v a • fun i => I.φ v (u i) := by
    funext i; simp
  simp only [vec, h, Matrix.mulVec_smul]

def mulL (c : InfinitePlace I.F → ℂ) :
    (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun x := fun v i => c v * x v i
  map_add' x w := by
    funext v i; simp [mul_add]
  map_smul' r x := by
    funext v i; simp [Complex.real_smul]; ring

variable {I}

def mulMat {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ mulL I c ∘ₗ ρ.symm.toLinearMap)

theorem mulMat_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) (w : Fin N → ℝ) :
    mulMat ρ c *ᵥ w = ρ (mulL I c (ρ.symm w)) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem mulMat_adj {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) (a b : Fin N → ℝ) :
    (mulMat ρ c *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (mulMat ρ (fun v => starRingEnd ℂ (c v)) *ᵥ b) := by
  rw [mulMat_mulVec, mulMat_mulVec]
  have hb : b = ρ (ρ.symm b) := (ρ.apply_symm_apply b).symm
  have ha : a = ρ (ρ.symm a) := (ρ.apply_symm_apply a).symm
  conv_lhs => rw [hb]
  conv_rhs => rw [ha]
  rw [hρ, hρ]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [mulL, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def]
  ring_nf

theorem mulMat_transpose {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) :
    (mulMat ρ c)ᵀ = mulMat ρ (fun v => starRingEnd ℂ (c v)) := by
  classical
  ext i j
  have := mulMat_adj ρ hρ c (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single, single_dotProduct] using this

end MulCoord
end GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.MulCoord

theorem gm_mul {N : ℕ} {I : AutInst} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (w : I.E) (M : Matrix (Fin N) (Fin N) ℤ)
    (hM : ∀ j, w • e j = ∑ i, M i j • e i) :
    gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = mulMat ρ (fun v => I.φ v w) * gm I ρ y e := by
  ext i j
  have hcol : (fun k => gm I ρ y e k j) = ρ (vec I y (e j)) := by funext k; rfl
  have hR : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j = ρ (vec I y (w • e j)) i := by
    have h1 : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j =
        (mulMat ρ (fun v => I.φ v w) *ᵥ fun k => gm I ρ y e k j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, hcol, mulMat_mulVec, LinearEquiv.symm_apply_apply]
    have h2 : mulL I (fun v => I.φ v w) (vec I y (e j)) = vec I y (w • e j) := by
      funext v k
      rw [vec_smul]
      rfl
    rw [h2]

  rw [hR, hM j, vec_sum_zsmul, map_sum, Finset.sum_apply]
  simp only [map_zsmul]
  simp only [Matrix.mul_apply, Matrix.map_apply, Pi.smul_apply, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gm, Matrix.of_apply]
  ring

theorem mul_conj_coord : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)),
    IsRealCoord I ρ → ∀ α : I.E, IsIntegral ℤ α → ∃ X : Matrix (Fin N) (Fin N) ℝ,
      ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ M M' : Matrix (Fin N) (Fin N) ℤ,
        gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = X * gm I ρ y e ∧
        gm I ρ y e * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * gm I ρ y e ∧ ∀ j, α • e j = ∑ i, M i j • e i := by
  classical
  intro I N ρ hρ α hα
  refine ⟨mulMat ρ (fun v => I.φ v α), ?_⟩
  intro y e he
  have hint : ∀ j, IntVec I (e j) := fun j => (he.2 _).2 ⟨Pi.single j 1, by
    simp [Pi.single_apply, ite_smul]⟩
  have hα' : IsIntegral ℤ (star α) := by
    exact hα.map (starRingEnd I.E).toIntAlgHom
  have hz : ∀ j, ∃ z : Fin N → ℤ, α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (α • e j)).1 fun i => by simpa [smul_eq_mul] using hα.mul (hint j i)
  have hz' : ∀ j, ∃ z : Fin N → ℤ, star α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (star α • e j)).1 fun i => by simpa [smul_eq_mul] using hα'.mul (hint j i)
  choose z hz using hz
  choose z' hz' using hz'
  have hM : ∀ j, α • e j = ∑ i, (Matrix.of fun i j => z j i) i j • e i := fun j => by
    simpa using hz j
  have hM' : ∀ j, star α • e j = ∑ i, (Matrix.of fun i j => z' j i) i j • e i := fun j => by
    simpa using hz' j
  refine ⟨Matrix.of fun i j => z j i, Matrix.of fun i j => z' j i, gm_mul ρ y e α _ hM, ?_, hM⟩
  rw [mulMat_transpose ρ hρ, gm_mul ρ y e (star α) _ hM']
  congr 2
  funext v
  exact I.cm.cmUnram.2.1 (I.φ v) α

end GlobalTheory.CuspGeo.MulCoord
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')

      rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
end
