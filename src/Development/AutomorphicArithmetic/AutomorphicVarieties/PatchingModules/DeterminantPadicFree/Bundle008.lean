module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle005
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Blocks

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private def bd (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    Matrix (Fin (a + b)) (Fin (a + b)) R :=
  (fromBlocks A 0 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private theorem bd_mul (A A' : Matrix (Fin a) (Fin a) R) (D D' : Matrix (Fin b) (Fin b) R) :
    bd A D * bd A' D' = bd (A * A') (D * D') := by
  simp [bd, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem bd_one : bd (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  simp [bd]

private theorem bd_transpose (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D)ᵀ = bd Aᵀ Dᵀ := by
  simp [bd, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

private theorem bd_map (f : R →+* S) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).map f = bd (A.map f) (D.map f) := by
  unfold bd
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

private theorem bd_smul (c : R) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    c • bd A D = bd (c • A) (c • D) := by
  unfold bd
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp

private theorem bd_ll (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    bd A D (Fin.castAdd b i) (Fin.castAdd b j) = A i j := by
  simp [bd]

private theorem bd_rr (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    bd A D (Fin.natAdd a i) (Fin.natAdd a j) = D i j := by
  simp [bd]

private theorem bd_inj {A A' : Matrix (Fin a) (Fin a) R} {D D' : Matrix (Fin b) (Fin b) R}
    (h : bd A D = bd A' D') : A = A' ∧ D = D' := by
  constructor
  · ext i j; rw [← bd_ll A D, h, bd_ll]
  · ext i j; rw [← bd_rr A D, h, bd_rr]

private theorem bd_det (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).det = A.det * D.det := by
  simp [bd]

private theorem bd_mem (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    bd A D ∈ Ev R R (a + b) a := by
  intro i j
  refine ⟨fun _ => trivial, fun h => ?_⟩
  rw [Submodule.mem_bot]
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h ⊢

private theorem bd_ex {M : Matrix (Fin (a + b)) (Fin (a + b)) R} (h : M ∈ Ev R R (a + b) a) :
    ∃ A D, M = bd A D := by
  refine ⟨M.submatrix (Fin.castAdd b) (Fin.castAdd b), M.submatrix (Fin.natAdd a) (Fin.natAdd a), ?_⟩
  ext i j
  have h' := (h i j).2
  rw [Submodule.mem_bot] at h'
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h' ⊢ <;> exact h'

private def bdU (A : GL (Fin a) R) (D : GL (Fin b) R) : GL (Fin (a + b)) R :=
  ⟨bd A.val D.val, bd A⁻¹.val D⁻¹.val, by rw [bd_mul, Units.mul_inv, Units.mul_inv, bd_one],
    by rw [bd_mul, Units.inv_mul, Units.inv_mul, bd_one]⟩

private def bdRep {G : Type} [Group G] (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R) :
    G →* GL (Fin (a + b)) R where
  toFun g := bdU (r₁ g) (r₂ g)
  map_one' := Units.ext (by
    show bd (r₁ 1).val (r₂ 1).val = 1
    rw [map_one, map_one, Units.val_one, Units.val_one, bd_one])
  map_mul' g h := Units.ext (by
    show bd (r₁ (g * h)).val (r₂ (g * h)).val = bd (r₁ g).val (r₂ g).val * bd (r₁ h).val (r₂ h).val
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, bd_mul])

private theorem rep_ex {G : Type} [Group G] (r : G →* GL (Fin (a + b)) R)
    (h : ∀ g, mat r g ∈ Ev R R (a + b) a) :
    ∃ (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R), ∀ g, (r g).val = bd (r₁ g).val (r₂ g).val := by
  choose A D hAD using fun g => bd_ex (h g)
  have h1 : bd (A 1) (D 1) = bd 1 1 := by rw [← hAD, map_one, bd_one]
  have hm : ∀ g g', bd (A (g * g')) (D (g * g')) = bd (A g * A g') (D g * D g') := fun g g' => by
    rw [← bd_mul, ← hAD, ← hAD, ← hAD, map_mul]
  let A' : G →* Matrix (Fin a) (Fin a) R := ⟨⟨A, (bd_inj h1).1⟩, fun g g' => (bd_inj (hm g g')).1⟩
  let D' : G →* Matrix (Fin b) (Fin b) R := ⟨⟨D, (bd_inj h1).2⟩, fun g g' => (bd_inj (hm g g')).2⟩
  exact ⟨A'.toHomUnits, D'.toHomUnits, fun g => hAD g⟩

end Blocks

theorem UpperTheory.V.Pa.Det.twoBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {n : ℕ} (a : ℕ) (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin n) (FractionRing (PowerSeries K))) (H : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → a ≤ n → (∀ g, mat r g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a) → H ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∃ (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin n) (PowerSeries K')), (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) ∧ (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈ Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a ∧ ∀ g, mat r' g ∈ Ev (PowerSeries K') (PowerSeries K') n a := by
  intro K K' G _ _ _ n a j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hX hsq hd hb hH hdet hσ hr ha hev hHev
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨H₁, H₂, rfl⟩ := bd_ex hHev
  obtain ⟨r₁, r₂, hrr⟩ := rep_ex r hev
  rw [bd_transpose] at hH
  rw [bd_det] at hdet
  have hr' : ∀ g, bd ((mat r₁ g)ᵀ * H₁ * mat r₁ (σ g)) ((mat r₂ g)ᵀ * H₂ * mat r₂ (σ g)) =
      bd (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₁)
        (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₂) := fun g => by
    rw [← bd_smul, ← hr g, ← bd_mul, ← bd_mul, ← bd_transpose]
    show _ = ((r g).val)ᵀ * _ * (r (σ g)).val
    rw [hrr, hrr]
    rfl
  obtain ⟨Q₁, s₁, hQ₁, hs₁⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₁ H₁ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.castAdd b i) (Fin.castAdd b i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₁ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_ll])
    (bd_inj hH).1 (left_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).1)
  obtain ⟨Q₂, s₂, hQ₂, hs₂⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₂ H₂ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.natAdd a i) (Fin.natAdd a i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₂ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_rr])
    (bd_inj hH).2 (right_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).2)
  refine ⟨bdU Q₁ Q₂, bdRep s₁ s₂, ?_, fun g => Units.ext ?_, bd_mem _ _, fun g => bd_mem _ _⟩
  · show (bd Q₁.val Q₂.val)ᵀ * _ * bd Q₁.val Q₂.val = 1
    rw [bd_map, bd_transpose, bd_mul, bd_mul, hQ₁, hQ₂, bd_one]
  · have e₁ : (r₁ g).val.map (f₂.comp f₁) * Q₁.val = Q₁.val * (s₁ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₁ g)
    have e₂ : (r₂ g).val.map (f₂.comp f₁) * Q₂.val = Q₂.val * (s₂ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₂ g)
    show (r g).val.map (f₂.comp f₁) * bd Q₁.val Q₂.val =
      bd Q₁.val Q₂.val * (bd (s₁ g).val (s₂ g).val).map (algebraMap _ (FractionRing (PowerSeries K')))
    rw [hrr, bd_map, bd_map, bd_mul, bd_mul, e₁, e₂]
end

section

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa

section Coc

variable {R G : Type} [CommRing R] [Group G] {n : ℕ} (χ : G → R) (r : G → Matrix (Fin n) (Fin n) R)

def dTw (Y : Matrix (Fin n) (Fin n) R) (g : G) : Matrix (Fin n) (Fin n) R := χ g • (r g * Y * r g⁻¹) - Y

def TwCoc (S : Set G) (z : G → Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, z (g * h) = z g + χ g • (r g * z h * r g⁻¹)

def cV (a : ℕ) (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) < a ∧ ¬ (j : ℕ) < a then Z i j else 0

def cV' (a : ℕ) (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if ¬ (i : ℕ) < a ∧ (j : ℕ) < a then Z i j else 0

end Coc

structure DetFr (F G : Type) [Field F] [Group G] (n : ℕ) where
  two : (2 : F) ≠ 0
  a : ℕ
  a_pos : 1 ≤ a
  a_le : a ≤ n
  G' : Subgroup G
  comm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ G'
  χ : G →* Fˣ
  χ_triv : ∀ g ∈ G', χ g = 1
  g₀ : G
  χ_ne : χ g₀ ≠ 1
  r : G →* Matrix (Fin n) (Fin n) F
  span : Submodule.span F (r '' (G' : Set G)) = Ev F F n a
  ev : ∀ g, r g ∈ Ev F F n a
  σ : G →* G
  σσ : ∀ g, σ (σ g) = g
  χσ : ∀ g, χ (σ g) = χ g
  μ : G → Fˣ
  form : ∀ g, (r g)ᵀ * r (σ g) = (μ g : F) • (1 : Matrix (Fin n) (Fin n) F)

namespace DetFr

variable {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)

abbrev χF (g : G) : F := D.χ g

def KillsRel (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) : Prop :=
  ∀ c : G →₀ F, (∀ g ∈ c.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 →
    (c.sum fun g x => x • (z g * D.r g)) i j = 0

structure IsKap {m : ℕ} (κ : Fin m → G → Matrix (Fin n) (Fin n) F) : Prop where
  coc : ∀ j, TwCoc (fun _ => 1) D.r Set.univ (κ j)
  od : ∀ j g, κ j g ∈ Od F F n D.a
  pol : ∀ j g, κ j (D.σ g) = -(κ j g)ᵀ
  indep : ∀ (c : Fin m → F) (Y), Y ∈ Od F F n D.a → Yᵀ = -Y → (∀ g, ∑ j, c j • κ j g = dTw (fun _ => 1) D.r Y g) → c = 0

structure IsTw {m : ℕ} (κ : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F)
    (la : Fin m → G → Matrix (Fin n) (Fin n) F) : Prop where
  sq : s * s = 1
  coc : ∀ j, TwCoc D.χF D.r Set.univ (la j)
  od : ∀ j g, la j g ∈ Od F F n D.a
  pol : ∀ j g, la j (D.σ g) = s • (la j g)ᵀ
  ev : ∀ g, ph g ∈ Ev F F n D.a
  ph_mul : ∀ g h, ph (g * h) = ph g + D.χF g • (D.r g * ph h * D.r g⁻¹ +
    ∑ j, (κ j g * (D.r g * la j h * D.r g⁻¹) - (D.r g * la j h * D.r g⁻¹) * κ j g))
  ph_pol : ∀ g, ph (D.σ g) = s • (ph g)ᵀ
  ell : ∀ g ∈ D.G', (ph g * D.r g).trace + ∑ j, (la j g * κ j g * D.r g).trace = 0

end DetFr

variable {l : ℕ} [Fact l.Prime]

def NP.Ext2 {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A) : Prop :=
  x.Ext x' j ∧ (∀ v, x'.w v = GeneralLinearGroup.map j (x.w v)) ∧ x'.ty = x.ty

def etaM {X : Type} {g n : ℕ} (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X := Z.map DD.eta

def ep'M {X : Type} {g n : ℕ} (j : Fin g) (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X :=
  Z.map fun d => d.ep' j

class IsEqDVR (l : outParam ℕ) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : Prop where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  finite : Finite (IsLocalRing.ResidueField A)
  char : CharP A l

end UpperTheory.V.Pa
end
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem l_zero {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) : (l : K) = 0 := by
  by_contra hne
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hlp : ringChar K ≠ l := by
    intro h
    apply hne
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  have hcop : l.Coprime (ringChar K) := (Nat.coprime_primes (Fact.out) hp).mpr hlp.symm
  have hu : IsUnit ((ringChar K : ℕ) : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have hu' := hu.map f
  rw [map_natCast, ringChar.Nat.cast_ringChar] at hu'
  exact not_isUnit_zero hu'

private theorem hom_uniq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R) (h : (l : R) = 0) :
    f = f' := by
  ext x
  have hx := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  have hx' : x = (PadicInt.zmodRepr x : ℤ_[l]) + y * l := by rw [hy]; ring
  rw [hx', map_add (f := _), map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast, h]
  simp

private theorem localization_quotient_separated_dvd {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] (g : A →+* L)
    (hi : Function.Injective g) (P : Polynomial A) (hs : (P.map (algebraMap A K)).Separable) :
    (P.map g).Separable := by
  have hP : P.map g = (P.map (algebraMap A K)).map (IsFractionRing.lift hi) := by
    rw [Polynomial.map_map]
    congr 1
    ext a
    simp [IsFractionRing.lift_algebraMap]
  rw [hP]
  exact hs.map

private theorem sep_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (j : A →+* B)
    (hinj : Function.Injective j) (P : Polynomial A) (hs : (P.map (algebraMap A (FractionRing A))).Separable) :
    ((P.map j).map (algebraMap B (FractionRing B))).Separable := by
  rw [Polynomial.map_map]
  exact localization_quotient_separated_dvd (K := FractionRing A) ((algebraMap B (FractionRing B)).comp j)
    ((IsFractionRing.injective B (FractionRing B)).comp hinj) P hs

theorem UpperTheory.V.Pa.Det.coefficientExtension_preserves_conditions_and_det :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext x' j → (∀ D : Subgroup F.G₀, x.N4 D → x'.N4 D) ∧ (x.N3 → x'.N3) ∧ GDet.ofRep (mat x'.ρ) = (GDet.ofRep (mat x.ρ)).map j := by
  intro l _ F n x x' j hE
  obtain ⟨hinj, hloc, hfin, hρ, ha, hψ⟩ := hE
  have hmat : ∀ g, mat x'.ρ g = (mat x.ρ g).map j := by
    intro g
    rw [hρ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Dg h4 Z hZ
    obtain ⟨m, b, p, hm, hsum, hlin, hdual, -, -⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
    have h0 : ((l : ℕ) : x'.A) = 0 := by
      simpa using congrArg (PowerSeries.C (R := x'.K)) (l_zero (algebraMap ℤ_[l] x'.K))
    have hj : algebraMap ℤ_[l] x'.A = j.comp (algebraMap ℤ_[l] x.A) := hom_uniq _ _ h0
    have heps : ∀ g, ((F.eps ℤ_[l] x'.A g : x'.Aˣ) : x'.A) = j (F.eps ℤ_[l] x.A g : x.Aˣ) := by
      intro g
      simp [GFrame.eps, pushCh, hj]
    have hZi : ∀ i, Z.map (p i) = 0 := by
      intro i
      apply h4
      intro g hg
      have lhs : ∀ (e : x.A) (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (j e * ∑ k, j (M a k) * Z k c) = e * ∑ k, M a k * p i (Z k c) := by
        intro e M a c

        rw [Finset.mul_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul, hlin, mul_assoc]
      have rhs : ∀ (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (∑ k, Z a k * j (M k c)) = ∑ k, p i (Z a k) * M k c := by
        intro M a c

        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, hlin, mul_comm]
      ext a c
      have hac := congrFun (congrFun (hZ g hg) a) c
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, hmat, Matrix.map_apply, heps] at hac
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.map_apply]
      rw [← lhs, ← rhs, hac]
    ext a c
    have hz : ∀ i, p i (Z a c) = 0 := by
      intro i
      have h1 := congrFun (congrFun (hZi i) a) c
      simpa only [Matrix.map_apply, Matrix.zero_apply] using h1
    rw [hsum (Z a c), Matrix.zero_apply]
    simp [hz]
  · intro h3 U hU hne
    obtain ⟨σ, hσ, hsep⟩ := h3 U hU hne
    refine ⟨σ, hσ, ?_⟩
    rw [hmat, Matrix.charpoly_map]
    exact sep_map j hinj _ hsep
  · apply GDet.ext
    intro B _ _ y
    show Matrix.det _ = Matrix.det _
    congr 1
    simp only [MonoidHom.coe_coe, AlgHom.coe_toRingHom, GDet.repAlg]
    congr 2
    apply congrArg
    ext g a b
    simp [hmat]
    try rfl
end
