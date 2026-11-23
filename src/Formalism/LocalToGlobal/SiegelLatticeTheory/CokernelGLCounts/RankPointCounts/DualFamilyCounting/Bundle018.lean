module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SemidefG
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualLeGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

@[expose] public section

section

noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TotPosAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), star x = x → Formalism.MainNotions.S.LocalSplitGroups.TotPos x → Formalism.HermitianLattices.Ext.L3.TotPos x

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_comb' {ι : Type} [Fintype ι] (p : ι → S.V) (A : Matrix ι ι E) (b c : ι) :
    S.hT (∑ a, A a b • p a) (∑ a, A a c • p a) =
      (A.conjTranspose * Matrix.of (fun a a' => S.hT (p a) (p a')) * A) b c := by

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
  Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, starRingEnd_apply, Finset.sum_mul,
  Finset.mul_sum]
  first
    | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)

variable {r : ℕ}

def gv (y : Fin r → S.V) (z : S.V) (N : ℕ) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) y ((-((N : E)⁻¹)) • z)


variable (E) in
def Gam (r N' : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -(N' : E) else 0

def Gam' (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  (Z⁻¹).conjTranspose * Gam E r N' * Z⁻¹

def Psi (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (d : Fin r) (a : Fin (r + 1)) : E :=
  if a = Fin.last r then Gam' N' Z (Fin.castSucc d) (Fin.last r) else Gam' N' Z (Fin.castSucc d) a / 2

def pv (e y : Fin r → S.V) (z : S.V) (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w0 : S.V)
    (a : Fin (r + 1)) : S.V :=
  gv y z N a + ∑ d, Psi N' Z d a • e d + (if a = Fin.last r then (1 : E) else 0) • w0

def tv (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Gam' N' Z (Fin.last r) (Fin.last r) + (N : E)⁻¹

theorem gam_herm (N' : ℕ) (a b : Fin (r + 1)) : star (Gam E r N' a b) = Gam E r N' b a := by
  simp only [Gam, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem gam'_herm (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    star (Gam' N' Z a b) = Gam' N' Z b a := by
  have hG : (Gam E r N').conjTranspose = Gam E r N' := by
    ext a b; rw [Matrix.conjTranspose_apply, gam_herm]
  have h1 : (Gam' N' Z).conjTranspose = Gam' N' Z := by
    simp only [Gam', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  have := congrFun (congrFun h1 b) a
  rwa [Matrix.conjTranspose_apply] at this

variable {e y : Fin r → S.V} {z : S.V} {N : ℕ} (h : Dual e y z N) (hN : 0 < N)
include h hN

theorem hgv_e (a : Fin (r + 1)) (d : Fin r) :
    S.hT (gv y z N a) (e d) = if a = Fin.castSucc d then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last d).ne']
    simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.ez d), smul_zero]
  | cast a =>
    simp only [gv, Fin.snoc_castSucc, Fin.castSucc_inj, h.ye]
    by_cases had : a = d
    · subst had; simp
    · simp [had, Ne.symm had]

theorem he_gv (d : Fin r) (a : Fin (r + 1)) :
    S.hT (e d) (gv y z N a) = if a = Fin.castSucc d then 1 else 0 := by
  rw [hsw, hgv_e h hN]; split_ifs <;> simp

theorem hz_gv (a : Fin (r + 1)) : S.hT z (gv y z N a) = if a = Fin.last r then 1 else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    simp only [gv, Fin.snoc_last, map_smul, smul_eq_mul, h.zz, if_true]
    field_simp
  | cast a =>
    rw [if_neg (Fin.castSucc_lt_last a).ne]
    simp only [gv, Fin.snoc_castSucc]
    exact hsw0 S (h.yz a)

theorem hgv_gv (a a' : Fin (r + 1)) : S.hT (gv y z N a) (gv y z N a') =
    if a = Fin.last r ∧ a' = Fin.last r then -((N : E)⁻¹) else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, h.zz,
        starRingEnd_apply, star_neg, star_inv₀, star_natCast, and_self, if_true]
      field_simp
    | cast a' =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        hsw0 S (h.yz a'), smul_zero]
      simp [(Fin.castSucc_lt_last a').ne]
  | cast a =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, map_smul, h.yz, smul_zero]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast a' =>
      simp only [gv, Fin.snoc_castSucc, h.yy]
      simp [(Fin.castSucc_lt_last a).ne]

variable {N' : ℕ} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {w0 : S.V} (hw : IsW e y z w0)
include hw

theorem hf_pv (a a' : Fin (r + 1)) :
    S.hT (Fin.snoc (α := fun _ => S.V) e z a) (pv e y z N N' Z w0 a') = if a = a' then 1 else 0 := by
  obtain ⟨hwe, -, hwz⟩ := hw
  induction a using Fin.lastCases with
  | last =>

    simp only [pv, Fin.snoc_last, map_add (f := _), map_sum, map_smul, smul_eq_mul, hsw0 S (h.ez _), mul_zero,
    Finset.sum_const_zero, add_zero, hwz, hz_gv h hN]
    simp [eq_comm]
  | cast a =>

    simp only [pv, Fin.snoc_castSucc, map_add (f := _), map_sum, map_smul, smul_eq_mul, h.ee, mul_zero,
    Finset.sum_const_zero, add_zero, hwe, he_gv h hN]
    simp [eq_comm]

theorem hpv_pv (ht : S.hT w0 w0 = tv N N' Z) (a a' : Fin (r + 1)) :
    S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') = Gam' N' Z a a' := by
  obtain ⟨hwe, hwy, hwz⟩ := hw
  have hgw : ∀ b, S.hT (gv y z N b) w0 = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last => simp [gv, hwz]
    | cast b => simp [gv, hwy]
  have hwg : ∀ b, S.hT w0 (gv y z N b) = 0 := fun b => hsw0 S (hgw b)
  have hwe' : ∀ d, S.hT w0 (e d) = 0 := fun d => hsw0 S (hwe d)
  have key : S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') =
      S.hT (gv y z N a) (gv y z N a') +
      ∑ d, Psi N' Z d a' * S.hT (gv y z N a) (e d) +
      ∑ d, star (Psi N' Z d a) * S.hT (e d) (gv y z N a') +
      star (if a = Fin.last r then (1 : E) else 0) * (if a' = Fin.last r then (1 : E) else 0) * S.hT w0 w0 := by

    simp only [pv, map_add (f := _), LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h.ee, mul_zero, Finset.sum_const_zero, hgw, hwg,
    hwe, hwe', add_zero, zero_add]
    ring
  rw [key, hgv_gv h hN, ht]
  simp only [hgv_e h hN, he_gv h hN, mul_ite, mul_one, mul_zero]
  have hne : ∀ d : Fin r, Fin.last r ≠ Fin.castSucc d := fun d => (Fin.castSucc_lt_last d).ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last => simp [tv, hne]
    | cast a' => simp [hne, Psi, gam'_herm]
  | cast a =>
    induction a' using Fin.lastCases with
    | last => simp [hne, (Fin.castSucc_lt_last a).ne, Psi]
    | cast a' =>
      simp [(Fin.castSucc_lt_last a).ne, (Fin.castSucc_lt_last a').ne, Psi, star_div₀, gam'_herm]

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter Matrix
open scoped TensorProduct

def AlgWitt : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S) (O : Subring S), (∀ z, s (s z) = z) → (∀ z ∈ O, s z ∈ O) →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → J' * J = 1 →
    (∀ i j, J i j ∈ O) → (∀ i j, J' i j ∈ O) →
    ∀ (a : ℕ) (β β' : Fin a → S), (∀ i, β i ∈ O) → (∀ i, β' i ∈ O) → (∀ i, β i * β' i = 1) →
    (∀ i, ∀ t ∈ O, ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (β i - s lam * t) * c' = 1) →
    ∀ (x y : Fin a → Fin n → S), (∀ i k, x i k ∈ O) → (∀ i k, y i k ∈ O) →
    (∀ i j, Formalism.UG.hform s J (x i) (x j) = if i = j then β i else 0) →
    (∀ i j, Formalism.UG.hform s J (y i) (y j) = if i = j then β i else 0) →
    ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i

def HermDiag : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ z, σ (σ z) = z) → (2 : K) ≠ 0 →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm σ J →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → K),
    (Matrix.of fun i j => Formalism.UG.hform σ J (X0 i) (X0 j)).det ≠ 0 →
    ∃ P Q : Matrix (Fin a) (Fin a) K, Q * P = 1 ∧
      (∀ i j, i ≠ j → Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P j l • X0 l) = 0) ∧
      ∀ i, Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P i l • X0 l) ≠ 0

def LamAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ δ : E, σ δ = δ → δ ≠ 0 →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ t ∈ OEv (E := E) v,
      ∃ lam ∈ OEv (E := E) v, lam * sigR (Fv F v) σ lam = 1 ∧
        ∃ c' ∈ OEv (E := E) v, (inclR (Fv F v) δ - sigR (Fv F v) σ lam * t) * c' = 1

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcLoc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OmLocU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → IsSDLoc σ J v Λ → UnramAt (E := E) v → a ≤ n → IsPrim v Λ Y →
  (∃ w ∈ OEv (E := E) v, (gramR (Fv F v) σ J Y).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J Y).det * w = 1) →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} =
      ENNReal.ofReal (absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (n - a + 1) n,
          (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

end Formalism.L2.SG.Pf.NcLoc
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcSplit

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def SplitOm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (r : ℕ)
    (P : Frame E n r) (MG : MeasG σ J r) (MW : MeasW σ J P)
    (hT : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j)
    (νH : Measure (Fin (r + 1 + r) → Fin n → AF F ⊗[F] E)) (Λ : Set (Fin n → E)),
    StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → (gramE σ J (tupH P)).det ≠ 0 → 2 * (r + 1 + r) < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.SWc1W F E σ n J → MG.IsTextNorm → MW.IsTextNorm →
    IsOmT F E σ n J ψ (gramE σ J (tupH P)) hT νH →
    IsCompatT F E σ n J (tupH P) MG.μG MW.μH νH →
    0 < MG.μGf (Kf σ J Λ) → MG.μGf (Kf σ J Λ) < ⊤ →
    ∃ a' : ℝ, 0 < a' ∧
      (AllSome (SdW F E σ n J (Ainf F) (psiInf F ψ) (r + 1 + r)) fun μinf =>
       AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) (r + 1 + r)) fun νinf =>
       AllSome (fun fibInf : HermR (Ainf F) σ (r + 1 + r) → Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) =>
         IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
           {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
       ∀ f : HA (Ainf F) σ J → ENNReal, Measurable f →
         ∀ s : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J,
           (∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (Ainf F) (tupH P) = y) → s y • ratTup (Ainf F) (tupH P) = y) →
           ∫⁻ g, f g ∂MG.μGinf = ENNReal.ofReal a' *
             ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf F) σ J)) ∂MW.μHinf
               ∂(fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))) ∧
      (MG.μGf (Kf σ J Λ)).toReal * a' =
        (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal *
          ∏' v : HeightOneSpectrum (𝓞 F),
            (omAt σ J ψ v ((gramE σ J (tupH P)).map (inclR (Fv F v)))
              {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) (tupH P)}).toReal

end Formalism.L2.SG.Pf.NcSplit
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

def InFib (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T Λ : Submodule (𝓞 K) V) :
    Prop :=
  (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

theorem mem_W_of_prO_zero {x : V} (hx : prO hc x = 0) : x ∈ orthK h U ∧ prO hc.symm x = x := by
  have e := prO_add hc x
  rw [hx, zero_add] at e
  refine ⟨?_, e⟩
  rw [← e]
  rw [prO_apply]
  first
  | exact Submodule.projection_apply_mem ..
  | exact Submodule.projection_apply_mem _ _
  | exact Submodule.projection_apply_mem _ _ _
  | exact Submodule.projection_apply_mem _
  | simp

theorem prO_symm_locF (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {y : V} (hy : y ∈ locF 𝔭 N) :
    prO hc.symm y ∈ locF 𝔭 (N.map (prO hc.symm)) := by
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp N y).mp hy
  refine (LocF.mem_locF_iff hp _ _).mpr ⟨t, ht, ?_⟩
  have hs := (prO hc.symm).map_smul (algebraMap (𝓞 F) (𝓞 K) t) y
  rw [← hs]
  exact Submodule.mem_map_of_mem hty

theorem glue_mem [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hG₀ : Good hc M T 𝔭 Λ₀) (h0 : InFib h U 𝔭 M T Λ₀)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) (hsurj : Function.Surjective P) :
    InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
  have hp := h𝔭.isPrime
  obtain ⟨⟨N₀, hN₀, hΛ₀⟩, hd₀, -, -⟩ := h0
  have hd : dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) = glue hc T 𝔭 Λ₀ P :=
    le_antisymm (dual_le_glue hs hG₀ hd₀ hM hT hP hsurj) (glue_le_dual hs hd₀ hP)
  have hIU := glue_inf_U hG₀ hd₀ hP
  have hIW := glue_inf_orthK_eq_locF (P := P) hG₀
  refine ⟨?_, hd, hIU, hIW⟩
  have hspan : Submodule.span K (↑(M ⊔ T) : Set V) = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le (Submodule.span_mono (show M ≤ M ⊔ T from le_sup_left))
      (Submodule.span_mono (show T ≤ M ⊔ T from le_sup_right))
  have hMT : Submodule.IsFullLattice K (M ⊔ T) :=
    { toIsLattice := Submodule.IsLattice.of_fg K (hM.1.sup hT.1)
      span_eq_top := hspan }
  refine exists_lattice_locF h𝔭 hMT (L₂ := N₀ ⊔ N₀.map (prO hc.symm))
    (hN₀.fg.sup (hN₀.fg.map _)) ?_ ?_ ?_
  · conv_lhs => rw [← hd]
    rw [locF_dualF h𝔭, hd]
  · refine sup_le ?_ ?_
    · intro m hm
      have : m ∈ locF 𝔭 M := LocF.le_locF 𝔭 M hm
      rw [← hIU] at this
      exact this.1
    · intro m hm
      have : m ∈ locF 𝔭 T := LocF.le_locF 𝔭 T hm
      rw [← hIW] at this
      exact this.1
  · rintro x ⟨b, hb, y, hy, c, hcy, hU, hPc⟩
    obtain ⟨z, hz, hzb⟩ := hG₀.oW b b.2
    have hyN : y ∈ locF 𝔭 N₀ := hΛ₀ ▸ hy
    have hzN : z ∈ locF 𝔭 N₀ := hΛ₀ ▸ hz
    have ex : x = y - prO hc.symm y + prO hc.symm z := by
      have e3 : prO hc y = y - prO hc.symm y := eq_sub_of_add_eq (prO_add hc y)
      calc x = prO hc x + prO hc.symm x := (prO_add hc x).symm
        _ = prO hc y + prO hc.symm z := by rw [hU, hzb, hb]
        _ = _ := by rw [e3]
    rw [ex]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact LocF.locF_mono 𝔭 le_sup_left hyN
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hyN)
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hzN)

def isoOf (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) :
    Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) :=
  ((gam hG₀).symm.trans (gam hG)).toLinearMap

theorem isoOf_mk (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) {y w : V} (hy : y ∈ Λ₀) (hw : w ∈ Λ)
    (hwU : prO hc w = prO hc y) :
    isoOf hG₀ hG (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm w, hG.iW w hw⟩ := by
  have key : ∀ {Λ' : Submodule (𝓞 K) V} (hG' : Good hc M T 𝔭 Λ') (b : Λ'),
      gam hG' (toDisc h hc M Λ' 𝔭 hG'.iU b) = toDisc h hc.symm T Λ' 𝔭 hG'.iW b := by
    intro Λ' hG' b
    unfold gam
    simp only [LinearEquiv.trans_apply]
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ' 𝔭 hG'.iU)
        (toDisc_surj h hc M Λ' 𝔭 hG'.iU hG'.oU) b, LinearEquiv.symm_apply_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have h1 : (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩ : DiscMod h (orthK h U) T 𝔭) =
      gam hG₀ (toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩) := (key hG₀ ⟨y, hy⟩).symm
  have h2 : toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩ = toDisc h hc M Λ 𝔭 hG.iU ⟨w, hw⟩ :=
    congrArg Submodule.Quotient.mk (Subtype.ext hwU.symm)
  unfold isoOf
  rw [h1]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [h2]
  exact key hG ⟨w, hw⟩

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem absNorm_small_finite (D : Formalism.BasicNotions.D7) :
    {p : PlF D | (Ideal.absNorm p.asIdeal : ℝ) < 3}.Finite := by
  have h : {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I < 3}.Finite := by
    have : {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I < 3} =
        ⋃ n ∈ Finset.range 3, {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I = n} := by
      ext I; simp [Finset.mem_range]
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => Ideal.finite_setOf_absNorm_eq n)
  refine (h.preimage (fun p _ q _ hpq => IsDedekindDomain.HeightOneSpectrum.ext hpq)).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact_mod_cast hp

end Formalism.L2.SG.Pf.Cnt
end
end
