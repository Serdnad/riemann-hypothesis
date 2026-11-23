module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle161
public import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands


open scoped Pointwise in
theorem exists_compact_mod_unipB_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → (∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : V, x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1) → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ v : V, ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g : GL (Fin m) k, l (ρ (corner g) v) ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c := by
  intro k _ _ _ _ ψ hψc hψ1 m V _ _ ρ hs hJ l hl v
  have hcm : ∀ g h : GL (Fin m) k, corner (g * h) = corner g * corner h := fun g h => by
    simp only [corner]
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hcc : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
    (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))
  have hdc : Continuous (diagT k (Fin m)) :=
    (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin m))
  set X : Set V := (fun g => ρ g v) '' (corner '' (KO k (Fin m) : Set (GL (Fin m) k))) with hX
  have hXf : X.Finite := GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt _ V ρ v (hs v) _ (GlobalTheory.SplitFlip.isCompact_KO.image hcc)
  choose r1 hr1 using GlobalTheory.T.whittaker_functional_torus_valuation_bound k ψ hψc hψ1 (m + 1) V ρ hs l hl
  have hlow : ∀ (x : V) (i : Fin m), ∃ r : kˣ, ∀ t : Fin (m + 1) → kˣ,
      l (ρ (diagT k (Fin (m + 1)) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) := by
    intro x i
    have hi := i.2
    have h : ∑ j, ![(i : ℕ) + 1, m - i] j = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact GlobalTheory.T.whittaker_torus_twKer_rootBound' k ψ hψc (m + 1) V ρ l hl _ _ h i.castSucc i.succ (by simp) (by simp) x
      (hJ _ _ h (Nat.succ_pos _) (by omega) x)
  choose r2 hr2 using hlow
  choose R1 R2 hR using fun x => GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds k m (fun _ => r1 x) (r2 x)
  refine ⟨⋃ x ∈ X, diagT k (Fin m) '' {t : Fin m → kˣ | ∀ i, valuation k (R2 x : k) ≤ valuation k (t i : k) ∧
      valuation k (t i : k) ≤ valuation k (R1 x : k)} * (KO k (Fin m) : Set (GL (Fin m) k)),
    hXf.isCompact_biUnion fun x _ => ((GlobalTheory.T.isCompact_boundedTorus' k m (R1 x) (R2 x)).image hdc).mul GlobalTheory.SplitFlip.isCompact_KO,
    fun g hg => ?_⟩
  obtain ⟨u, hu, t, κ, hκ, rfl⟩ := GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral k m g
  have hcu := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
  rw [hcm, hcm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl _ hcu.1, GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one] at hg
  have hg' := right_ne_zero_of_mul hg
  have hxX : ρ (corner κ) v ∈ X := ⟨corner κ, ⟨κ, hκ, rfl⟩, rfl⟩
  have hlast : (Fin.snoc t 1 : Fin (m + 1) → kˣ) (Fin.last m) = 1 := Fin.snoc_last _ _
  have hb := hR _ _ hlast (fun i => ⟨hr2 _ i _ hg', hr1 _ _ i.castSucc i.succ (by simp) hg'⟩)
  refine ⟨u, hu, diagT k (Fin m) t * κ, Set.mem_biUnion hxX ⟨_, ⟨t, fun i => ?_, rfl⟩, κ, hκ, rfl⟩,
    mul_assoc _ _ _⟩
  have := hb i.castSucc
  simpa [Fin.snoc_castSucc] using this

end GlobalTheory.LocLanglands
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def IsNeg (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Prop := (-(Yᴴ * Jm P Q * Y)).PosDef

def matA (Y : Matrix (Ix P Q) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ := Y.toRows₁ * (Y.toRows₂)⁻¹

def linX (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim (v ∘ Sum.inl - matA Y *ᵥ (v ∘ Sum.inr)) ((φ ∘ Sum.inl) ᵥ* matA Y + φ ∘ Sum.inr)

def scal (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) : ℂ :=
  (Y.toRows₂.det)⁻¹ * Complex.exp (-((linX Y v φ ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)))

def ker (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ)
    (v' φ' : Ix P Q → ℂ) : ℂ :=
  ((-(Yᴴ * Jm P Q * Y')).det)⁻¹ * Complex.exp ((star v ᵥ* Jm P Q) ⬝ᵥ v' -
    (star v ᵥ* Jm P Q + φ') ⬝ᵥ (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) *ᵥ (Jm P Q *ᵥ star φ + v'))

def baseY (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Ix P Q) (Fin Q) ℂ := Matrix.fromRows A 1

def baseV (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim (x ∘ Sum.inl) 0

def baseF (x : Ix P Q → ℂ) : Ix P Q → ℂ := Sum.elim 0 (x ∘ Sum.inr)

def dA (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) : Matrix (Fin P) (Fin Q) ℂ :=
  Z.toBlocks₁₁ * A + Z.toBlocks₁₂ - A * (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)

def dX (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : Ix P Q → ℂ :=
  Sum.elim ((Z.toBlocks₁₁ - A * Z.toBlocks₂₁) *ᵥ (x ∘ Sum.inl))
    (-((x ∘ Sum.inr) ᵥ* (Z.toBlocks₂₁ * A + Z.toBlocks₂₂)))

def dS (Z : Mat P Q) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : ℂ :=
  -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂).trace - (x ∘ Sum.inr) ⬝ᵥ Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)

theorem toRows₂_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : (baseY A).toRows₂ = 1 := rfl

theorem matA_baseY (A : Matrix (Fin P) (Fin Q) ℂ) : matA (baseY A) = A := by
  simp [matA, baseY]

theorem linX_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : linX (baseY A) (baseV x) (baseF x) = x := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  have h2 : baseF x ∘ Sum.inl = 0 := rfl
  rw [linX, h1, h2]
  ext (i | j) <;> simp [baseV, baseF]

theorem scal_base (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) : scal (baseY A) (baseV x) (baseF x) = 1 := by
  have h1 : baseV x ∘ Sum.inr = 0 := rfl
  simp [scal, h1, toRows₂_baseY]

theorem form_blocks (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * Y'.toRows₂ - Y.toRows₁ᴴ * Y'.toRows₁ := by
  conv_lhs => rw [← Matrix.fromRows_toRows Y, ← Matrix.fromRows_toRows Y']
  rw [Jm, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem frame_eq (Y : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) :
    Y = baseY (matA Y) * Y.toRows₂ := by
  rw [baseY, Matrix.fromRows_mul, matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one,
    Matrix.one_mul, Matrix.fromRows_toRows]

theorem form_factor (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det) (h' : IsUnit Y'.toRows₂.det) :
    -(Yᴴ * Jm P Q * Y') = Y.toRows₂ᴴ * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
  have e : ∀ Y : Matrix (Ix P Q) (Fin Q) ℂ, IsUnit Y.toRows₂.det → matA Y * Y.toRows₂ = Y.toRows₁ := fun Y h => by
    rw [matA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  rw [form_blocks, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    e Y h, Matrix.mul_assoc, e Y' h']

theorem isNeg_baseY {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) : IsNeg (baseY A) := by
  rw [IsNeg, form_blocks]
  simpa [baseY] using h

theorem IsNeg.isUnit {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : IsUnit Y.toRows₂.det := by
  rw [IsNeg, form_blocks] at h
  have h2 := h.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self Y.toRows₁)
  rw [sub_add_cancel] at h2
  have h3 := h2.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

theorem IsNeg.posDef {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) : (1 - (matA Y)ᴴ * matA Y).PosDef := by
  have hu := h.isUnit
  rw [IsNeg, form_factor Y Y hu hu] at h
  have hu' : IsUnit Y.toRows₂ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact (hu'.posDef_star_left_conjugate_iff).1 h

theorem form_mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) :
    (g * Y)ᴴ * Jm P Q * (g * Y') = Yᴴ * Jm P Q * Y' := by
  rw [Matrix.conjTranspose_mul]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

theorem IsNeg.mul {g : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) {Y : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) :
    IsNeg (g * Y) := by
  rwa [IsNeg, form_mul hg]

theorem Jm_mul_Jm : Jm P Q * Jm P Q = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem ker_mul {g g' : Mat P Q} (hg : gᴴ * Jm P Q * g = Jm P Q) (hg' : g' * g = 1)
    (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : Ix P Q → ℂ) :
    ker (g * Y) (g *ᵥ v) (φ ᵥ* g') (g * Y') (g *ᵥ v') (φ' ᵥ* g') = ker Y v φ Y' v' φ' := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg'
  have h1 : gᴴ * Jm P Q = Jm P Q * g' := by
    conv_rhs => rw [← hg, Matrix.mul_assoc, hg2, Matrix.mul_one]
  have h0 : g' = Jm P Q * gᴴ * Jm P Q := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have hJ : (Jm P Q)ᴴ = Jm P Q := by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h2 : Jm P Q * g'ᴴ = g * Jm P Q := by
    rw [h0, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have e1 : star (g *ᵥ v) ᵥ* Jm P Q = (star v ᵥ* Jm P Q) ᵥ* g' := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h1]
  have e2 : Jm P Q *ᵥ star (φ ᵥ* g') = g *ᵥ (Jm P Q *ᵥ star φ) := by
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
  have e3 : g * Y' * (Yᴴ * Jm P Q * Y')⁻¹ * (g * Y)ᴴ * Jm P Q =
      g * (Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q) * g' := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h1]
  have e4 : ∀ (u w : Ix P Q → ℂ) (M : Mat P Q), (u ᵥ* g') ⬝ᵥ (g * M * g') *ᵥ (g *ᵥ w) = u ⬝ᵥ M *ᵥ w := by
    intro u w M
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg', Matrix.mul_one]
  rw [ker, ker, form_mul hg, e1, e2, e3, ← Matrix.add_vecMul, ← Matrix.mulVec_add, e4, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]

end GlobalTheory.OscGauss

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetEx

theorem exists_finset_sdLat_reps : ∀ (X : Fields), X.Ok → ∀ n : ℕ, ∃ T : Finset (Submodule (𝓞 X.E) (Sp X.E n)), (∀ N ∈ T, IsSdLat N) ∧ ∀ N : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat N → ∃ N₀ ∈ T, ∃ γ : UF X.E n, N = gmap γ.1 N₀ := by
  intro X hX n
  obtain ⟨s, hs, H⟩ := unimod_finite (E := X.E) (posStar_of_conj hX.conjE) n
  refine ⟨s, hs, fun N hN => ?_⟩
  obtain ⟨N₀, h₀, g, hg, e⟩ := H N hN.1 hN.2
  exact ⟨N₀, h₀, ⟨g, hg⟩, e.symm⟩

end GlobalTheory.Mem.Col2.JetEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

def OffRow (g : GL (Fin n) Rv) : Prop :=
  (∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v) ∧
    ∀ j, j ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j = ιv pE * s

theorem offRow_col {g : GL (Fin n) Rv} (hg : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (hi : OffRow n (π := π) v g⁻¹) (i : Fin n) (hne : i ≠ lastIdx n) :
    ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s := by
  have h1 := rll_inv_entry hc n v (Subgroup.inv_mem _ hg) i (lastIdx n)
  rw [inv_inv] at h1
  obtain ⟨s, hs, e⟩ := hi.2 i hne
  refine ⟨_, rll_sigV_mem hc v hs, ?_⟩
  rw [h1, e, map_mul, rll_sigV_incl]

variable (h : BasePi ST π)
include h

theorem offRow_maps_L {g : GL (Fin n) Rv} (hg : OffRow n (π := π) v g) (z : Fin n → Rv)
    (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  have hzi : ∀ j, z j ∈ 𝒪v := fun j => by
    by_cases hj : j = lastIdx n
    · subst hj
      rw [← rll_p_mul_pinv v h (z (lastIdx n))]
      exact mul_mem (rll_incl_int v π) h2
    · exact h1 j hj
  refine ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    exact sum_mem fun j _ => mul_mem (hg.1 i j) (hzi j)
  show ιv pE⁻¹ * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  by_cases hj : j = lastIdx n
  · subst hj
    rw [mul_left_comm]; exact mul_mem (hg.1 _ _) h2
  · obtain ⟨s, hs, e⟩ := hg.2 j hj
    rw [e, mul_assoc, rll_pinv_mul v h]
    exact mul_mem hs (h1 j hj)

theorem offRow_maps_Ker {g : GL (Fin n) Rv} (hg : OffRow n (π := π) v g)
    (hcol : ∀ i, i ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s)
    (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE))) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE)) := by
  have hq : star pE / pE ≠ 0 := div_ne_zero h.star_ne_zero h.coe_ne_zero
  have key : ιv (star pE) = ιv (star pE / pE) * ιv pE := by
    rw [← map_mul, div_mul_cancel₀ _ h.coe_ne_zero]
  have hcp : ιv (star pE) ∈ 𝒪v := rll_incl_int v (cO E π)
  rw [rll_mem_loc_dLat n v _ hq] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  constructor
  · intro i hi
    show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      obtain ⟨s, hs, e⟩ := hcol i hi
      have e2 : (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) * z (lastIdx n) =
          ιv pE * s * (ιv (star pE / pE) * z (lastIdx n)) := by
        rw [e, key]; ring
      rw [e2]
      exact mul_mem (mul_mem (rll_incl_int v π) hs) h2
    · exact mul_mem (hg.1 i j) (h1 j hj)
  · show ιv (star pE / pE) * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
    rw [Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      rw [mul_left_comm]; exact mul_mem (hg.1 _ _) h2
    · obtain ⟨s, hs, e⟩ := hg.2 j hj
      have e2 : ιv (star pE / pE) * ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j) = ιv (star pE) * (s * z j) := by
        rw [e, key]; ring
      rw [e2]
      exact mul_mem hcp (mul_mem hs (h1 j hj))

end Loc

theorem unitary_offRow_stab_three :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  intro F E _ _ _ _ _ _ hc n _ ST π h v g hU h1 h2
  have hr1 : OffRow n (π := π) v g := h1
  have hr2 : OffRow n (π := π) v g⁻¹ := h2
  have hUi := Subgroup.inv_mem _ hU
  have hcol := offRow_col hc n v hU hr2
  have hcol' := offRow_col hc n v hUi (by rw [inv_inv]; exact hr1)
  refine ⟨?_, ?_, ?_⟩
  · rw [rll_baseLb_eq n h]
    exact rll_stab_of_maps _ g (offRow_maps_L n v h hr1) (offRow_maps_L n v h hr2)
  · rw [rll_dualV_eq hc n v h]
    exact rll_stab_of_maps _ g (rll_maps_Sh n v h hr1.1 hcol) (rll_maps_Sh n v h hr2.1 hcol')
  · rw [rll_baseKer_eq n h]
    exact rll_stab_of_maps _ g (offRow_maps_Ker n v h hr1 hcol) (offRow_maps_Ker n v h hr2 hcol')

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.level_acts_trivially_on_discriminant_group : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (_ : (q : E) = σ (p : E)) (_ : (p : E) * (q : E) = (T : E)) (_ : T ≠ 0)
    (_ : S.Lb = rll_dLat n ((p : E)⁻¹))
    (_ : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (_ : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ S.Uloc v),
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  first | exact @GlobalTheory.uloc_acts_trivially_on_dual_quotient | exact GlobalTheory.uloc_acts_trivially_on_dual_quotient | (intros; apply GlobalTheory.uloc_acts_trivially_on_dual_quotient <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

abbrev IncreasingRowChoicePerColumn (N : ℕ) (Y : YoungDiagram) : Type := ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N

def sig {Lt : Type} (N : ℕ) (s : Lt) : Fin N × Fin N → Lt × ℕ × Fin N := fun v => (s, (v.2 : ℕ), v.1)

theorem map_nablaX {Lt : Type} [Fintype Lt] (K : Type) [CommRing K] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : WeylLatticeDuality.ColChoice N nu) :
    map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rename (sig N s) (GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  simp [sig]

theorem colLen_le_of_rowLen {N : ℕ} {Y : YoungDiagram} (h : Y.rowLen N = 0) : Y.colLen 0 ≤ N := by
  by_contra hc'
  have hc := not_le.mp hc'
  have h1 : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr hc
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  omega

end GlobalTheory.WeylLatDualProof
end
end
