module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConTwist

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commGroup_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' : C) : a * b' = a * b * (b' * b⁻¹) := by
  rw [mul_assoc, mul_comm b' b⁻¹, mul_inv_cancel_left]

theorem commGroup_mul_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' e : C) : a * b' * e = a * b * e * (b' * b⁻¹) := by
  rw [commGroup_mul_eq_mul_mul_div a b b', mul_right_comm]

theorem chrS_mu (t t' : T) (i j : ℕ) :
    G.chrS (.mu t' i j) = G.chrS (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrS, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

theorem chrT_mu (t t' : T) (i j : ℕ) :
    G.chrT (.mu t' i j) = G.chrT (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrT, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isDetRoot_one {V V' : HSp D} {y : (AE D)ˣ} (hy : IsDetRoot V 1 y) : IsDetRoot V' 1 y := by
  simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at hy ⊢
  exact hy

theorem contr_smul_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL f₁ (c • f₂) = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL (c • f₁) f₂ = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem lastBi_smul {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (c : ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    GlobalTheory.FinPl.lastBi o o'' τ (c • Ξ) Φ₂ = c • GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ := by
  funext u v
  simp only [GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_mu_twist (W : G.Weil) (t t' : T) (k : ℕ) (hk : k + 1 ≤ D.R.m) {a : GA D (G.V (.grid D.R.m k))}
    {b : GA D (G.V (.grid D.R.m (k + 1)))} {y y' : (AE D)ˣ} (hy : IsDetRoot _ a y) (hy' : IsDetRoot _ b y')
    {f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) :
    W.om (.mu t' D.R.m k) (a, b) f =
      ((((L.xi t' * (L.xi t)⁻¹) y)⁻¹ * (L.xi t' * (L.xi t)⁻¹) y' : Circle) : ℂ) • W.om (.mu t D.R.m k) (a, b) f := by
  have h0 := W.om_is (.mu t D.R.m k) ⟨le_rfl, hk⟩
  have h1 := W.om_is (.mu t' D.R.m k) ⟨le_rfl, hk⟩
  rw [chrS_mu t t', chrT_mu t t'] at h1
  exact GlobalTheory.TupRoot.twist_eq h0 h1 hy hy' hf

theorem fock_theta (W : G.Weil) (ρ : RealMatch W) (t : T) (P : PolDown G) (k : ℕ) (hk : k < D.R.m) :
    IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1)))
      (fockD W t (fun j => ρ.vT D.R.m j) P ⟨k, hk⟩) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (ρ.vT_is t D.R.m k le_rfl hk).2.theta _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem contr_flat_twist {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ)
    (vL : VolM D B'.L.rank J.W₀.rank) (X : WO B.V J.W → ℂ) (Y : WO J.W B'.V → ℂ) (c₁ c₂ : ℂ) :
    contr l J.W₀ vL (flatBF s₁ (c₁ • X)) (flatFB s₂ (c₂ • Y)) =
      (c₁ * c₂) • contr l J.W₀ vL (flatBF s₁ X) (flatFB s₂ Y) := by
  rw [GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul, contr_smul_left, contr_smul_right, smul_smul, mul_comm]

theorem lastDat_twist (W : G.Weil) {t t' : T} {M M' : Vol G} (hM : M.Is t) (hM' : M'.Is t') (j : ℕ)
    (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (c : ℂ)
    (he : W.om (.mu t' D.R.m j) (g, 1) Φ₁ = c • W.om (.mu t D.R.m j) (g, 1) Φ₁) :
    lastDat W hM' j hj vN g Φ₁ Φ₂ = c • lastDat W hM j hj vN g Φ₁ Φ₂ := by
  have k1 := congrArg (flatBF (lastAt G W t' hM' j hj vN).s) he
  have k2 := GlobalTheory.HandHom.flatBF_smul (lastAt G W t' hM' j hj vN).s c (W.om (.mu t D.R.m j) (g, 1) Φ₁)
  have k := k1.trans k2
  unfold lastDat
  erw [k]
  erw [lastBi_smul]
  rfl

theorem conAt_twist (W : G.Weil) (ρ : RealMatch W) (t t' : T) (M M' : Vol G) (hM : M.Is t) (hM' : M'.Is t')
    (P : PolDown G) (h : Pts G) (x : ℕ → (AE D)ˣ) (hx : ∀ k, IsDetRoot _ (h k) (x k)) (hm : h D.R.m = 1) (j : ℕ)
    (hjm : j < D.R.m) :
    conAt W hM' (fockD W t' (fun j => ρ.vT D.R.m j) P) h j =
      ((((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
        conAt W hM (fockD W t (fun j => ρ.vT D.R.m j) P) h j := by
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · simp only [conAt, h0, ↓reduceDIte]
    have hr : IsDetRoot (G.V (.grid D.R.m (j + 1))) 1 (x D.R.m) := isDetRoot_one (hm ▸ hx D.R.m)
    exact lastDat_twist W hM hM' j h0 _ _ _ _ _
      (om_mu_twist W t t' j (by omega) (hx j) hr (fock_theta W ρ t' P j (by omega)))
  by_cases h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m
  · simp only [conAt, h0, h1, ↓reduceDIte]
    have e1 := om_mu_twist W t t' j (by omega) (hx j) (hx (j + 1)) (fock_theta W ρ t' P j (by omega))
    have e2 : W.om (.mu t' D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) =
        ((((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
          W.om (.mu t D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) :=
      om_mu_twist W t t' (j + 1) (by omega) (hx (j + 1)) (hx (j + 2)) (fock_theta W ρ t' P (j + 1) (by omega))
    erw [e1, e2]
    refine (contr_flat_twist (J := jacAt G hM' (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ _ _ _ _ _ _ _).trans ?_
    rw [← Circle.coe_mul]
    have hc : ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 1)) *
        (((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2))) =
        ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) := by
      group
    rw [hc]
    rfl
  · simp only [conAt, h0, h1, ↓reduceDIte, smul_zero]

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

theorem conAt_twist_big : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t t' : T) (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') (P : PolDown ch.G) (h : Pts ch.G) (x : ℕ → (AE D)ˣ), (∀ k, IsDetRoot _ (h k) (x k)) → h D.R.m = 1 → ∀ j, Even j → j < D.R.m → conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) h j = ((((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x j))⁻¹ * (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) h j := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t t' M M' hM hM' P h x hx hm j _ hjm
  exact conAt_twist ch.W ch.rm t t' M M' hM hM' P h x hx hm j hjm

end GlobalTheory.ConTwist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem prodRel_map {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (T : ∀ l, (X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, T l (g i l) (y l) = 0 := by
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ (⊤ : Submodule ℂ (X l → ℂ))) ∧
      ∀ u ∈ S.image (fun i => g i l), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.finset_functions_recovered_from_values ⊤ _ (fun _ _ => Submodule.mem_top)
  choose s E _ hE using hkey
  have h1 : ∀ i ∈ S, ∏ l, T l (g i l) (y l) =
      ∑ ξ ∈ Fintype.piFinset s, (∏ l, g i l (ξ l)) * ∏ l, T l (E l (ξ l)) (y l) := by
    intro i hi
    have h2 : ∀ l, T l (g i l) (y l) = ∑ x ∈ s l, g i l x * T l (E l x) (y l) := by
      intro l
      conv_lhs => rw [hE l (g i l) (Finset.mem_image_of_mem _ hi)]

      simp [map_sum, Finset.sum_apply]
    simp only [h2]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i hi, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h ξ, zero_mul]

theorem prodRel_allSome {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, f i l (y l) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  choose T hT using fun l => (hf i₀ hi₀ l).1
  rw [← prodRel_map S x g T h y]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [fun l => (hf i hi l).2 _ (hT l)]

theorem prodRel_allSome₂ {ι κ I : Type} [Fintype ι] [Fintype κ] {X Y : ι → Type} {X' Y' : κ → Type} (S : Finset I) (x : I → ℂ)
    (g : I → ∀ l, X l → ℂ) (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (g' : I → ∀ l, X' l → ℂ) (f' : I → ∀ l, Y' l → ℂ) (Q' : ∀ l, ((X' l → ℂ) →ₗ[ℂ] (Y' l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (hf' : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q' l) fun T => f' i l = T (g' i l))
    (h : ∀ (z : ∀ l, X l) (z' : ∀ l, X' l), ∑ i ∈ S, x i * ((∏ l, g i l (z l)) * ∏ l, g' i l (z' l)) = 0)
    (y : ∀ l, Y l) (y' : ∀ l, Y' l) :
    ∑ i ∈ S, x i * ((∏ l, f i l (y l)) * ∏ l, f' i l (y' l)) = 0 := by
  simp only [← mul_assoc]
  refine prodRel_allSome S (fun i => x i * ∏ l, f i l (y l)) g' f' Q' hf' (fun z' => ?_) y'
  have := prodRel_allSome S (fun i => x i * ∏ l, g' i l (z' l)) g f Q hf (fun z => by
    rw [← h z z']
    exact Finset.sum_congr rfl fun i _ => by ring) y
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem unfolded_eq_of_local_eq : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R Fc _ ch _ _ hcon t e _ τ φ hτ α SA xA F Gd fr fd hA hloc M hM P h u y
  have key := hcon t M hM P h ((SchRow ch.G × SchDown ch.G t) ⊕ α) (τ.support.disjSum SA)
    (Sum.elim (fun d => τ d) fun a => -xA a) (Sum.elim (fun d => d.1) fr) (Sum.elim (fun d => d.2) fd) ?_ ?_ u y
  · rw [Finset.sum_disjSum] at key
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    exact add_neg_eq_zero.mp key
  · intro i hi j
    have hv := (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta
    rcases i with d | a
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hτ d (by simpa using hi)).2 j).2 hv
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hA a (by simpa using hi)).2 j).2 hv
  · intro y v
    refine prodRel_allSome₂ (τ.support.disjSum SA) (Sum.elim (fun d => τ d) fun a => -xA a)
      (Sum.elim (fun d => (φ d).1) F) (Sum.elim (fun d => d.1) fr)
      (fun i => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.G.latS (.chi i D.R.m : Pair T) : Set _)
          (ch.G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.rm.vX i D.R.m))
      (Sum.elim (fun d => (φ d).2) Gd) (Sum.elim (fun d => d.2) fd)
      (fun j => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) (ch.G.latS (.mu t D.R.m j : Pair T) : Set _)
          (ch.G.latT (.mu t D.R.m j : Pair T) : Set _) fun _ => True) 1 (ch.rm.vT D.R.m j)) ?_ ?_ ?_ y v
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).1 l).2
      · exact ((hA a (by simpa using hi)).1 l).2
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).2 l).2
      · exact ((hA a (by simpa using hi)).2 l).2
    · intro z z'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← mul_assoc]
      exact add_neg_eq_zero.mpr (hloc z z')

end GlobalTheory.LocAsm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConnectionLinear
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem conAt_zero (hM : M.Is t) (Φ : SchDown G t) (h : Pts G) (j : ℕ) (hj : Even j) (hm : ¬ (Even D.R.m ∧ j + 2 ≤ D.R.m)) :
    conAt W hM Φ h j = 0 := by
  unfold conAt
  split_ifs with h1 h2
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h1]; simpa [Nat.even_add] using hj
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h2]; obtain ⟨r, hr⟩ := hj; exact ⟨r + ((D.R.m - 4 - j) / 2 + 1) + 1, by omega⟩
  · exact dif_neg h2

theorem conAt_local (hM : M.Is t) (Φ Φ' : SchDown G t) (h : Pts G) (j : ℕ)
    (hΦ : ∀ a : Fin D.R.m, ((a : ℕ) = j ∨ (a : ℕ) = j + 1) → Φ a = Φ' a) : conAt W hM Φ h j = conAt W hM Φ' h j := by
  have key : ∀ (a : ℕ) (ha : a < D.R.m), (a = j ∨ a = j + 1) → Φ ⟨a, ha⟩ = Φ' ⟨a, ha⟩ := fun a ha e => hΦ ⟨a, ha⟩ e
  unfold conAt
  simp (disch := simp) only [key]

theorem sum_eq_zero_of_multilin {ι I : Type} [Fintype ι] [dI : DecidableEq ι] {Y : ι → Type} (V : ∀ j, Submodule ℂ (Y j → ℂ))
    (E : (∀ j, Y j → ℂ) → ℂ)
    (hE : ∀ Φ : ∀ j, Y j → ℂ, (∀ j, Φ j ∈ V j) → ∀ a (φ φ' : Y a → ℂ) (c : ℂ), φ ∈ V a → φ' ∈ V a →
      E (Function.update Φ a (c • φ + φ')) = c * E (Function.update Φ a φ) + E (Function.update Φ a φ'))
    (S : Finset I) (x : I → ℂ) (Φ : I → ∀ j, Y j → ℂ) (hΦ : ∀ i ∈ S, ∀ j, Φ i j ∈ V j)
    (h0 : ∀ v : ∀ j, Y j, ∑ i ∈ S, x i * ∏ j, Φ i j (v j) = 0) : ∑ i ∈ S, x i * E (Φ i) = 0 := by
  have coe_upd : ∀ (m : ∀ j, V j) (a : ι) (p : V a),
      (fun j => ((Function.update m a p j : V j) : Y j → ℂ)) = Function.update (fun j => (m j : Y j → ℂ)) a (p : Y a → ℂ) :=
    fun m a p => funext fun j => Function.apply_update (fun j (z : V j) => (z : Y j → ℂ)) m a p j
  let Mm : MultilinearMap (RingHom.id ℂ) (fun j => V j) ℂ :=
    { toFun := fun m => E fun j => (m j : Y j → ℂ)
      map_update_add' := by
        intro inst m a p q
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_add]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p q 1 p.2 q.2
        rw [one_smul, one_mul] at this
        exact this
      map_update_smul' := by
        intro inst m a c p
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_smul, smul_eq_mul]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p 0 c p.2 (V a).zero_mem
        rw [add_zero] at this
        rw [this]
        have h00 := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a 0 0 1 (V a).zero_mem (V a).zero_mem
        simp only [smul_zero, add_zero, one_mul] at h00
        have hz : E (Function.update (fun j => (m j : Y j → ℂ)) a 0) = 0 := by linear_combination -h00
        rw [hz, add_zero]; rfl }
  classical
  let φ : I → ∀ j, V j := fun i j => if hi : i ∈ S then ⟨Φ i j, hΦ i hi j⟩ else 0
  let τ : I →₀ ℂ := Finsupp.onFinset S (fun i => if i ∈ S then x i else 0) (fun i hi => by by_contra h; simp [h] at hi)
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V Mm τ 0 φ φ (fun z => by
    rw [Finsupp.sum_zero_index, Finsupp.onFinset_sum _ (fun _ => zero_mul _)]
    rw [← h0 z]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [φ, hi])
  rw [Finsupp.sum_zero_index] at key
  dsimp only [τ] at key
  rw [Finsupp.onFinset_sum _ (g := fun a c => c • Mm (φ a)) (fun _ => zero_smul _ _)] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [φ, hi, Mm]
end GlobalTheory.ConnectionLinear

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def PositionLinAt (j off : ℕ) : Prop :=
  ∀ t (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (Φ : SchDown ch.G t) (a : Fin D.R.m), (a : ℕ) = j + off →
    ∀ (φ φ' : Sch ch.G (.down t D.R.m a)) (c : ℂ), (∀ b, IsThetaFunO ch.W.ψ _ _ (Φ b)) → IsThetaFunO ch.W.ψ _ _ φ →
      IsThetaFunO ch.W.ψ _ _ φ' → ∀ u v,
      conAt ch.W hM (fockD ch.W t (Function.update Φ a (c • φ + φ')) P) h j u v =
        c * conAt ch.W hM (fockD ch.W t (Function.update Φ a φ) P) h j u v +
          conAt ch.W hM (fockD ch.W t (Function.update Φ a φ') P) h j u v

def ContrLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 < D.R.m → Even D.R.m → PositionLinAt ch j off

def LastLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 = D.R.m → PositionLinAt ch j off

theorem conLin_of_positions (hC0 : ContrLin ch 0) (hC1 : ContrLin ch 1) (hL0 : LastLin ch 0) (hL1 : LastLin ch 1) :
    ConLin ch := by
  intro t M hM P h I S x f Φ hΦ h0 u y
  have intersection_update_fsHerm_neg_one : ∀ j off, Even j → off ≤ 1 → PositionLinAt ch j off := by
    intro j off hj ho
    by_cases hm : Even D.R.m ∧ j + 2 ≤ D.R.m
    · rcases Nat.lt_or_eq_of_le hm.2 with hlt | heq
      · interval_cases off
        · exact hC0 j hj hlt hm.1
        · exact hC1 j hj hlt hm.1
      · interval_cases off
        · exact hL0 j hj heq
        · exact hL1 j hj heq
    · intro t M hM P h Φ a _ φ φ' c _ _ _ u v
      simp only [conAt_zero ch.W hM _ h j hj hm, Pi.zero_apply, mul_zero, add_zero]
  let E : SchDown ch.G t → ℂ := fun Ψ => ∏ k ∈ Finset.range (D.R.m / 2),
    conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1))
  have hev : ∀ i, evT (conAt ch.W hM (fockD ch.W t (Φ i) P) h) (f i) u y = (∏ n, f i n (y n)) * E (Φ i) := fun i => by
    simp only [evT, E]; ring
  simp only [hev, ← mul_assoc]
  refine sum_eq_zero_of_multilin (fun j : Fin D.R.m => GlobalTheory.LastVertexInv.thSub ch.W (.mu t D.R.m (j : ℕ))) E ?_ S
    (fun i => x i * ∏ n, f i n (y n)) Φ (fun i hi j => hΦ i hi j) (fun v => ?_)
  · intro Ψ hΨ a φ φ' c hφ hφ'
    by_cases hm : Even D.R.m
    · have hk : (a : ℕ) / 2 ∈ Finset.range (D.R.m / 2) := by
        obtain ⟨r, hr⟩ := hm; have := a.2; rw [Finset.mem_range]; omega
      have hrest : ∀ ψ : Sch ch.G (.down t D.R.m a), ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) =
          ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) := by
        intro ψ
        refine Finset.prod_congr rfl fun k hk' => ?_
        have hk2 : k ≠ (a : ℕ) / 2 := by simpa using (Finset.mem_sdiff.1 hk').2
        rw [conAt_local ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) (fockD ch.W t Ψ P) h (2 * k) (fun b hb => ?_)]
        have hne : b ≠ a := fun e => by subst e; omega
        simp only [fockD, Function.update_of_ne hne]
      simp only [E]
      have hsplit := fun (g : ℕ → ℂ) => Finset.prod_eq_mul_prod_diff_singleton (s := Finset.range (D.R.m / 2)) ((a : ℕ) / 2) g (fun h' => absurd hk h')
      rw [hsplit, hsplit, hsplit, hrest, hrest, hrest]
      rw [intersection_update_fsHerm_neg_one (2 * ((a : ℕ) / 2)) ((a : ℕ) - 2 * ((a : ℕ) / 2)) (even_two_mul _) (by omega) t M hM P h Ψ a (by omega)
        φ φ' c hΨ hφ hφ']
      ring
    · have h0m : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; rw [Finset.mem_range]; omega
      have hz : ∀ Ψ' : SchDown ch.G t, E Ψ' = 0 := fun Ψ' => Finset.prod_eq_zero h0m (by
        rw [conAt_zero ch.W hM _ h (2 * 0) (even_two_mul 0) (fun e => hm e.1)]
        rfl)
      simp only [hz, mul_zero, add_zero]
  · rw [← h0 y v]
    exact Finset.sum_congr rfl fun i _ => by ring
end
end GlobalTheory.ConnectionLinear
end
end
