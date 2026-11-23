module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle046
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix UpperTheory.V.U3

private theorem conj_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ :=
  _root_.UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left h r g

private theorem conj_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) : (conjBy h r g).right = (r g).right :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalTranspose.conj_right h r g

private theorem conj_mat {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) (hg : (r g).right = 1) :
    (conjBy h r g).mat * (h : Matrix (Fin m) (Fin m) R) = (h : Matrix (Fin m) (Fin m) R) * (r g).mat := by
  unfold GG.mat
  rw [conj_left, hg, sgnAct_one, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul]

private theorem unit_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (hb : IsUnit b)
    (h : a - b ∈ IsLocalRing.maximalIdeal R) : IsUnit a := by
  by_contra ha
  have ha' : a ∈ IsLocalRing.maximalIdeal R := ha
  have : b ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ ha' h
  exact this hb

theorem UpperTheory.V.U3.normalised_unique :
    ∀ {G R : Type} [Group G] [CommRing R] [IsLocalRing R]
      (η : G →* ℤˣ) (Ψ : G →* (IsLocalRing.ResidueField R)ˣ) (c g₁ : G) (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R), IsUnit (2 : R) → Marks η Ψ c g₁ →
      (GG.map (IsLocalRing.residue R)).comp r = r0 η Ψ → CongOne (IsLocalRing.maximalIdeal R) h →
      Normalised c g₁ r → Normalised c g₁ (conjBy h r) → ∃ t : Rˣ, (t : R) - 1 ∈ IsLocalRing.maximalIdeal R ∧ h = tor R t := by
  intro G R _ _ _ η Ψ c g₁ r h h2 hM hred hc hN hN'
  have hright : ∀ g, (r g).right = η g := fun g => by
    have := congrArg (fun f : G →* GG (m := 3) (R := IsLocalRing.ResidueField R) => (f g).right) hred
    simpa using this
  have hrc : (r c).right = -1 := (hright c).trans hM.ηc
  have hrg : (r g₁).right = 1 := (hright g₁).trans hM.ηg
  have hrs : (r (gstar c g₁)).right = 1 := by
    rw [hright, gstar, map_mul, map_mul, map_inv, hM.ηc, hM.ηg]; simp
  have hz := zmat_diag r c g₁ h2 hrc hrg hN
  have hz' := zmat_diag (conjBy h r) c g₁ h2 ((conj_right h r c).trans hrc)
    ((conj_right h r g₁).trans hrg) hN'
  have hζ : IsUnit (zeta c g₁ r) := by
    have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ c g₁ hM).2
    rw [← hred] at h1
    have h3 : zeta c g₁ ((GG.map (IsLocalRing.residue R)).comp r) =
        IsLocalRing.residue R (zeta c g₁ r) := by
      simp [zeta, zmat]
    rw [h3] at h1
    exact (isUnit_map_iff _ _).1 h1
  have hcomm : zmat c g₁ (conjBy h r) * (h : Matrix (Fin 3) (Fin 3) R) =
      (h : Matrix (Fin 3) (Fin 3) R) * zmat c g₁ r := by
    rw [zmat, zmat, Matrix.sub_mul, Matrix.mul_sub, conj_mat h r _ hrg, conj_mat h r _ hrs]
  rw [hz, hz'] at hcomm
  generalize zeta c g₁ r = ζ at hζ hcomm
  generalize zeta c g₁ (conjBy h r) = ζ' at hcomm
  have he : ∀ a b, ![ζ', 0, -ζ'] a * h.val a b = h.val a b * ![ζ, 0, -ζ] b := fun a b => by
    have := congrFun (congrFun hcomm a) b
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have hd : ∀ a, h.val a a - 1 ∈ IsLocalRing.maximalIdeal R := fun a => by
    simpa using hc a a
  have hu0 : IsUnit (h.val 0 0) := unit_of_sub_mem isUnit_one (hd 0)
  have hζζ : ζ' = ζ := by
    have := he 0 0
    simp only [Matrix.cons_val_zero] at this
    exact hu0.mul_left_cancel (by rw [← this, mul_comm])
  subst hζζ
  have h2ζ : IsUnit (2 * ζ') := h2.mul hζ
  have e01 : h.val 0 1 = 0 := by
    have := he 0 1
    simp at this
    exact hζ.mul_left_cancel (by simpa using this)
  have e10 : h.val 1 0 = 0 := by
    have := he 1 0
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e12 : h.val 1 2 = 0 := by
    have := he 1 2
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination this)
  have e21 : h.val 2 1 = 0 := by
    have := he 2 1
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e02 : h.val 0 2 = 0 := by
    have := he 0 2
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination this)
  have e20 : h.val 2 0 = 0 := by
    have := he 2 0
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination -this)
  have hθ : theta h⁻¹ = h⁻¹ := by
    have h1 : (r c).left = 1 := Units.ext hN.atc
    have h3 : (conjBy h r c).left = 1 := Units.ext hN'.atc
    rw [conj_left, h1, hrc, sgnAct_neg_one, mul_one] at h3
    exact (eq_inv_of_mul_eq_one_right h3)
  have hJ : h.val * (Jmat R 3 * h.valᵀ * Jmat R 3) = 1 := by
    have := theta_val h⁻¹
    rw [hθ, inv_inv] at this
    rw [← this, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have p0 : h.val 0 0 * h.val 2 2 = 1 := by
    have := congrFun (congrFun hJ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have p1 : h.val 1 1 * h.val 1 1 = 1 := by
    have := congrFun (congrFun hJ 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have e11 : h.val 1 1 = 1 := by
    have hu : IsUnit (h.val 1 1 + 1) :=
      unit_of_sub_mem h2 (by convert hd 1 using 1; ring)
    exact hu.mul_left_cancel (by linear_combination p1)
  refine ⟨Units.mkOfMulEqOne _ _ p0, hd 0, Units.ext ?_⟩
  rw [tor_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wt1, e01, e10, e12, e21, e02, e20, e11, Units.mkOfMulEqOne]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.U3.Mop

theorem emb_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG (m := 3) (R := R))
    (a b : Fin 3 ⊕ Fin 3) : emb (GG.map f x) a b = f (emb x a b) := by
  have h : (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) =
      (theta x.left : Matrix (Fin 3) (Fin 3) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  show (if (GG.map f x).right = 1 then Matrix.fromBlocks (GG.map f x).mat 0 0 (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S)
    else Matrix.fromBlocks 0 (GG.map f x).mat (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) 0) a b =
    f ((if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) a b)
  rw [h, GG.map_mat, GG.map_right]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;> simp

theorem emb_push {O G R S : Type} [CommRing O] [Group G] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (r : G →* GG (m := 3) (R := R)) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (push f r g) a b = f (emb (r g) a b) := emb_map (f : R →+* S) (r g) a b

theorem emb_apply {R : Type} [CommRing R] (x : GG (m := 3) (R := R)) : emb x =
    if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0 := rfl

theorem mat_eq_emb {R : Type} [CommRing R] (x : GG (m := 3) (R := R)) (a b : Fin 3) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  rw [emb_apply]
  split_ifs <;> simp

theorem unitaryEmbedding_residualRep_eq_zero_of_weight_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  show (if (r0 η Ψ g).right = 1 then Matrix.fromBlocks (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) 0) a b = 0
  rw [theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

theorem blockWeight_sub_mem_Icc (a b : Fin 3 ⊕ Fin 3) : -2 ≤ wt6 a - wt6 b ∧ wt6 a - wt6 b ≤ 2 := by
  revert a b; decide

theorem origin_of {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (y : R →ₐ[O] O) (hy : ∀ s, y (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = y := by
  have key : ∀ F, y (W.π F) = MvPowerSeries.constantCoeff F := fun F => by
    have := GlobalTheory.algHom_sub_constantCoeff_mem (K := ⊥) (y.comp W.π) (fun s => hy s) F
    rw [Ideal.mem_bot, sub_eq_zero] at this
    exact this
  refine ⟨fun F hF => by rw [← key, hF, map_zero], AlgHom.ext fun x => ?_⟩
  obtain ⟨F, rfl⟩ := W.surj x
  exact (W.origin_π _ F).trans (key F).symm

theorem origin_presentation_var_eq_zero {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) (s : W.σ) : W.origin h (W.z s) = 0 := by
  rw [WPres.z, W.origin_π, MvPowerSeries.constantCoeff_X]

theorem mem_max_of_zero {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (x : R →ₐ[O] O) {z : R} (hz : x z = 0) :
    z ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, ← res_map (O := O) (R := R) (R' := O) x, hz, map_zero]

theorem base_coord {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {η : G →* ℤˣ} {Ψ : G →* Oˣ}
    {r : G →* GG (m := 3) (R := R)} {x : R →ₐ[O] O} (hx : push x r = r0 η Ψ) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    x (emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) = 0 := by
  rw [map_sub, AlgHom.commutes, ← emb_push, hx]
  exact sub_self _

theorem approx {O X R σ : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] [Finite σ] (wt : σ → X)
    (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R) (𝓑 : X → Submodule O R) (h1 : (1 : R) ∈ 𝓑 0)
    (hmul : ∀ i j, ∀ a ∈ 𝓑 i, ∀ b ∈ 𝓑 j, a * b ∈ 𝓑 (i + j))
    (hm : ∀ s, Φ (MvPowerSeries.X s) ∈ m) (hB : ∀ s, Φ (MvPowerSeries.X s) ∈ 𝓑 (wt s)) (j : X)
    (F : MvPowerSeries σ O) (hF : F ∈ wtPart O wt j) (n : ℕ) : ∃ y ∈ 𝓑 j, Φ F - y ∈ m ^ n := by
  classical
  refine ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem Φ hm n F⟩
  have hpow : ∀ s (k : ℕ), Φ (MvPowerSeries.X s) ^ k ∈ 𝓑 (k • wt s) := fun s k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ ih _ (hB s)
  have hmon : ∀ d : σ →₀ ℕ, (d.prod fun s k => Φ (MvPowerSeries.X s) ^ k) ∈ 𝓑 (Finsupp.weight wt d) := fun d => by
    induction d using Finsupp.induction_linear with
    | zero => simpa using h1
    | add f g hf hg =>
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), map_add (f := _)]
      exact hmul _ _ _ hf _ hg
    | single i k =>
      rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
      exact hpow i k

  rw [(MvPowerSeries.truncTotal n F).as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hw : Finsupp.weight wt d = j := by
    by_contra hne
    refine MvPolynomial.mem_support_iff.1 hd ?_
    by_cases hlt : Finsupp.degree d < n
    · rw [MvPowerSeries.coeff_truncTotal _ hlt]; exact hF d hne
    · exact MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.1 hlt)
  exact hw ▸ hmon d

def nEq {G R : Type} [Group G] [CommRing R] (c g₁ : G) (r : G →* GG (m := 3) (R := R)) : Fin 8 → R :=
  ![(r c).mat 0 0 - 1, (r c).mat 1 1 - 1, (r c).mat 0 1, (r c).mat 1 0, (r c).mat 0 2, (r c).mat 2 0,
    zmat c g₁ r 0 1, zmat c g₁ r 1 0]

def nWt : Fin 8 → ℤ := ![0, 0, 1, -1, 2, -2, 1, -1]

end UpperTheory.V.U3.Mop
end

section

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg MvPowerSeries

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {H : Type} [Group H] [TopologicalSpace H]
  {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R)

def IsBase {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (r : Γ →* GG (m := 3) (R := R))
    (x : R →ₐ[O] O) : Prop := push x r = r0 η Ψ

def ConjStable : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : GLift O η Ψ R) (h : GL (Fin 3) R),
    CongOne (maximalIdeal R) h → r'.hom = conjBy h r.hom → OnI U I R r → OnI U I R r'

def locDims (j : ℤ) : ℕ :=
  if j = -2 then 1 else if j = -1 then 2 else if j = 0 then 3 else if j = 1 then 4 else if j = 2 then 2 else 0

structure LocChart (x : U.R →ₐ[O] O) {τ : Type} (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)) :
    Prop where
  ker : RingHom.ker φ = I
  graded : ∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart (FractionRing O) w (wt a b)
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : U.R, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) →
    ∃ c : O, c ≠ 0 ∧ c • f ∈ RingHom.ker x ^ 2 ⊔ I

structure LocGood : Prop where
  conj : ConjStable U I
  chart : ∃ (x : U.R →ₐ[O] O) (τ : Type) (_ : Fintype τ) (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsBase η Ψ U.r.hom x ∧ LocChart U I x w φ ∧ ∀ j, Nat.card {i // w i = j} = locDims j

end Local

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {c g₁ : Γ}


variable (N hι U I c g₁) in
abbrev SRing : Type 1 := Univ (NormCond c g₁ (BoxCond N ι hι U I))

def EntWt {G R Q : Type} [Group G] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (r : G →* GG (m := 3) (R := R)) (j : ℤ)
    (D : R →ₗ[O] Q) : Prop := ∀ g a b, wt a b ≠ j → D ((r g).mat a b) = 0

structure Model (S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := c) (g₁ := g₁)) (K : Type) [NormedField K] [Algebra O K] : Type 1 where
  A : Type
  [cr : CommRing A]
  [al : Algebra O A]
  𝒜 : ℤ → Submodule O A
  [gr : GradedAlgebra 𝒜]
  x : A →ₐ[O] O
  wring : IsWRing 𝒜 x
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  m : ℕ
  Q : Eqns 𝒜 x r s r' s' m
  one_le : 1 ≤ r
  smooth : SmoothPt 𝒜 x (mDims r s r' s' m)
  q : A →ₐ[O] S.R
  ker_q : RingHom.ker q = Q.ideal
  x₀ : S.R →ₐ[O] O
  base : IsBase η Ψ S.r.hom x₀
  x₀_q : x₀.comp q = x
  ent : ∀ g a b, ∃ f ∈ 𝒜 (wt a b), q f = (S.r.hom g).mat a b
  dense : ∀ j, ∀ f ∈ 𝒜 j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon S.r.hom j), q f - y ∈ maximalIdeal S.R ^ n
  pts : M2 𝒜 Q.ideal → ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ →
    ∃ (t : Kˣ) (f : S.R →ₐ[O] K), IsLocPt f ∧ act 𝒜 (tz t) ξ = f.comp q
  der : M2 𝒜 Q.ideal → ∀ f : S.R →ₐ[O] K, IsLocPt f → ∀ D ∈ PtDer (f.comp q) K, (∀ y ∈ Q.ideal, D y = 0) →
    ∃ F : S.R →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y, (F (q y)).snd = D y
  lift : ∀ a : O, a ≠ 0 → ∀ D ∈ PtDer x₀ (O ⧸ Ideal.span {a}), EntWt S.r.hom (-1) D →
    ∀ xl : U.R →ₐ[O] O, IsBase (η.comp ι) (Ψ.comp ι) U.r.hom xl → ∀ D₁ ∈ PtDer xl O, (∀ y ∈ I, D₁ y = 0) →
    EntWt U.r.hom (-1) D₁ →
    (∀ h a' b', Ideal.Quotient.mk _ (D₁ ((U.r.hom h).mat a' b')) = D ((S.r.hom (ι h)).mat a' b')) →
    ∃ D' ∈ PtDer x O, HasWt 𝒜 (-1) D' ∧ ∀ f, D (q f) = Ideal.Quotient.mk _ (D' f)

attribute [instance] Model.cr Model.al Model.gr

def Model.len {S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := c) (g₁ := g₁)} {K : Type} [NormedField K] [Algebra O K] (M : Model S K) : ℕ∞ :=
  cotLen M.x M.𝒜 (-1) M.Q.F


variable (η) in
def TwoPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (r : Γ →* GG (m := 3) (R := R))
    (f : R →ₐ[O] K) : Prop := IsLocPt f ∧ ¬ Upper η (push f r) ∧ ¬ Lower η (push f r)

def CoversPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (η : Γ →* ℤˣ)
    (r : Γ →* GG (m := 3) (R := R)) (T : Finset (R →ₐ[O] K)) : Prop :=
  (∀ f ∈ T, TwoPt (η := η) r f) ∧ ∀ f : R →ₐ[O] K, TwoPt (η := η) r f → ∃ f' ∈ T, ∃ t : Kˣ, push f r = conjBy (tor (R := K) t) (push f' r)

def trDiff {R K : Type} [CommRing R] [Algebra O R] [CommRing K] [Algebra O K] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)
    (r : Γ →* GG (m := 3) (R := R)) (σ : Γ) (f : R →ₐ[O] K) : K :=
  f (r σ).mat.trace - algebraMap O K (r0 η Ψ σ).mat.trace


variable (η Ψ N ι c g₁) in
def shaCoc (a : O) : Set (Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})) :=
  {γ | IsLocallyConstant γ ∧ (∀ g, γ g ∈ gw (R := O ⧸ Ideal.span {a}) (-1)) ∧
    IsCoc ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧
    NormCoc c g₁ ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧ (∀ g ∈ N, γ g = 0) ∧
    ∃ X ∈ gw (R := O ⧸ Ideal.span {a}) (-1), ∀ h,
      γ (ι h) = cob ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) X (ι h)}

end Model

end UpperTheory.V.U3
end
end
