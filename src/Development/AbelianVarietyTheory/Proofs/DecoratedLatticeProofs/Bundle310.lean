module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle295
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

open scoped TensorProduct




namespace GlobalTheory.IwaOrbit

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_zero {P : Pl D → Prop} : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact mul_mem_intAE ha.2 hb.2⟩

theorem mulVec_mem_intAt {P : Pl D → Prop} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {z : Fin n → AE D}
    (hM : ∀ i j, M i j ∈ intAt D P) (hz : ∀ j, z j ∈ intAt D P) (i : Fin m) : (M *ᵥ z) i ∈ intAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_induction _ (· ∈ intAt D P) (fun _ _ => intAt_add) intAt_zero
    fun j _ => intAt_mul (hM i j) (hz j)

theorem mul_mem_idAt_left {P : Pl D → Prop} {l m n : ℕ} {A : Matrix (Fin l) (Fin m) (AE D)}
    (B : Matrix (Fin m) (Fin n) (AE D)) (hA : ∀ i j, A i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hA i k)

theorem mul_mem_idAt_right {P : Pl D → Prop} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (AE D))
    {B : Matrix (Fin m) (Fin n) (AE D)} (hB : ∀ i j, B i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hB k j)

theorem smul_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) : ε • X = X := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hX i j)

theorem smul_vec_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {n : ℕ}
    {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) : ε • y = y := by
  funext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hε _).1 (hy i)

theorem smul_mulVec' {m n : ℕ} (a : AE D) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D) :
    (a • A) *ᵥ y = a • (A *ᵥ y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem adj_smul {m n : ℕ} (a : AE D) (X : Matrix (Fin m) (Fin n) (AE D)) : adj (a • X) = cA D a • adj X := by
  ext i j
  change cA D (a * X j i) = cA D a * cA D (X j i)
  exact (cA D).map_mul _ _

theorem adj_sub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X - Y) = adj X - adj Y := by
  ext i j
  change cA D (X j i - Y j i) = cA D (X j i) - cA D (Y j i)
  exact (cA D).map_sub _ _

theorem adj_mem_idAt {P : Pl D → Prop} {ε : AE D} (hcε : cA D ε = ε) (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) (i : Fin n) (j : Fin m) :
    adj X i j ∈ idAt D P := by
  rw [hε]
  have h := congrArg (cA D) ((hε _).1 (hX j i))
  rw [(cA D).map_mul, hcε] at h
  exact h

theorem exists_onb (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (ht : Tame D v)
    (hεε : ε * ε = ε) (hcε : cA D ε = ε) (hεO : ε ∈ intAt D (· = v)) (hεI : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (hΛ : IsSDAt S v Λ) :
    ∃ b b' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, b i j ∈ idAt D (· = v)) ∧
      (∀ i j, b' i j ∈ idAt D (· = v)) ∧ b * b' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      b' * b = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (b' *ᵥ y) i ∈ intAt D (· = v))) ∧
      adj b * (gA S * b) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨β, β', hβ, hβ', h1, h2, hmem, hHO, hHc, hH⟩ := GlobalTheory.T.exists_unimodular_basis_selfDual_lattice_at_place D S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨P, P', hP, hP', hPP', hP'P, hPH⟩ := GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace D v ε S.rank _ ht hεε hcε hεO hεI hHO hHc hH
  refine ⟨β * P, P' * β', mul_mem_idAt_left P hβ, mul_mem_idAt_right P' hβ', ?_, ?_, ?_, ?_⟩
  · calc β * P * (P' * β') = β * (P * P') * β' := by simp only [Matrix.mul_assoc]
      _ = ε • (β * β') := by rw [hPP', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [h1, smul_smul, hεε]
  · calc P' * β' * (β * P) = P' * (β' * β) * P := by simp only [Matrix.mul_assoc]
      _ = ε • (P' * P) := by rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [hP'P, smul_smul, hεε]
  · intro y hy
    rw [hmem y hy]
    constructor
    · intro h i
      rw [← Matrix.mulVec_mulVec]
      exact mulVec_mem_intAt hP' h i
    · intro h i
      have hz : β' *ᵥ y = P *ᵥ (P' *ᵥ (β' *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, hPP', smul_mulVec', Matrix.one_mulVec,
          smul_vec_eq_self hεI (mulVec_mem_idAt β' hy)]
      rw [hz]
      exact mulVec_mem_intAt hP (fun j => by rw [Matrix.mulVec_mulVec]; exact h j) i
  · rw [adj_mul, ← hPH]
    simp only [Matrix.mul_assoc]

theorem selfDual_orbit : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  intro D S v Λ Λ' ht hΛ hΛ'
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨⟨ε, hεε, hcε, hεO, hεI, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  obtain ⟨b, b', hb, hb', hbb', hb'b, hmem, hG⟩ := exists_onb S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨c, c', hc, hc', hcc', hc'c, hmem', hG'⟩ := exists_onb S v ε Λ' ht hεε hcε hεO hεI hΛ'
  set g := c * b' with hg
  have hgI : ∀ i j, g i j ∈ idAt D (· = v) := mul_mem_idAt_right c hb'
  have hag : ε • adj g = adj g := smul_eq_self hεI (adj_mem_idAt hcε hεI hgI)
  have hgg : ε • g = g := smul_eq_self hεI hgI
  have hb'b' : adj b' * b' = ε • gA S := by
    have h := congrArg (fun X => adj b' * X * b') hG
    rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_self hεI (adj_mem_idAt hcε hεI hb')] at h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, hbb', adj_smul,
      adj_one, hcε, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hεε]
  have hf1 : adj g * (gA S * g) = ε • gA S := by
    rw [hg, adj_mul]
    calc adj b' * adj c * (gA S * (c * b')) = adj b' * (adj c * (gA S * c)) * b' := by simp only [Matrix.mul_assoc]
      _ = ε • gA S := by rw [hG', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb'b', smul_smul, hεε]
  have haG : adj g * gA S = ε • (adj g * gA S) := by rw [← Matrix.smul_mul, hag]
  have hGg : gA S * g = ε • (gA S * g) := by rw [← Matrix.mul_smul, hgg]
  have hunit : adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S := by
    show adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S
    rw [adj_add, adj_sub, adj_one, adj_smul, adj_one, hcε]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    rw [hf1]
    simp only [smul_add, smul_sub]
    rw [← haG, ← hGg, smul_smul, hεε]
    abel
  refine ⟨ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit, ?_, ?_⟩
  · refine (mem_congGrp_iff S (idAt D (· = v)) _).2 fun i j => ?_
    show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D (· = v)
    have e : (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j =
        g i j - ε * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact sub_mem (hgI i j) (Ideal.mul_mem_right _ _ hεO.1)
  · intro y hy
    have hMy : mt S (ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit) *ᵥ y = g *ᵥ y := by
      show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) *ᵥ y = g *ᵥ y
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec', Matrix.one_mulVec,
        smul_vec_eq_self hεI hy, sub_self, add_zero]
    rw [hMy, hmem y hy, hmem' _ (mulVec_mem_idAt g hy)]
    have : c' *ᵥ (g *ᵥ y) = b' *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mul_assoc, hc'c, Matrix.smul_mul, Matrix.one_mul,
        smul_eq_self hεI hb']
    rw [this]

end GlobalTheory.IwaOrbit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfCocycle

variable {D : D7} {S T : HSp D}

theorem comm4 {R : Type} [CommRing R] (c a h H : R) : c * (a * h * H) = c * a * H * h := by ring

theorem split_half {E R : Type} [Field E] [CharZero E] [CommRing R] (f : E →+* R) (x k : R) :
    x * k = x * (k * f ((2 : ℕ) : E)⁻¹) + x * (k * f ((2 : ℕ) : E)⁻¹) := by
  have h : f ((2 : ℕ) : E)⁻¹ * (1 + 1) = 1 := by
    rw [← map_one f, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination (-(x * k)) * h

theorem half_add {F R : Type} [Field F] [CharZero F] [CommRing R] (g : F →+* R) (t : R) :
    g (1 / 2) * (t + t) = t := by
  have h : g (1 / 2) * (1 + 1) = 1 := by
    rw [← map_one g, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination t * h

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  have h := GlobalTheory.LatVacSign.hO_smul_smul 1 a x y
  rwa [one_smul, one_mul] at h

theorem hO_nsmul_right (n : ℕ) (x y : WO S T) : hO S T x (n • y) = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hO_nsmul_left (n : ℕ) (x y : WO S T) : hO S T (n • x) y = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring



theorem char_symplOH_conjHalf_rest : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : ℕ), 0 < c → ∀ (Y Z : WO S T), c • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → Z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → e • Y = c • (e • Z) → ψ (symplOH S T (cA D e • Y) ((1 - cA D e) • Y)) = 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e SS he h2 c hc Y Z hY hZ heq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D (cA D e) = e := GlobalTheory.LatVac.cA_cA e
  have hP : ∀ PP ∈ SS, ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_ofNat]
    exact h2 PP hPP
  have hint : finPart D (e * incA D ((2 : ℕ) : D.host.E)⁻¹) ∈ intAE D :=
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.DatumFourier.idem_div_int he two_ne_zero hP)
  have hZ' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint Z hZ
  have hcA2 : cA D (incA D ((2 : ℕ) : D.host.E)⁻¹) = incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    change incA D (star ((2 : ℕ) : D.host.E)⁻¹) = _
    rw [star_inv₀, star_natCast]
  have k1 : hO S T (cA D e • Y) ((1 - cA D e) • Y) = (c : AE D) * cA D e * hO S T Y Z := by
    have a1 := GlobalTheory.LatVacSign.hO_smul_smul (cA D e) (1 - cA D e) Y Y
    have a2 := hO_smul_right e Y Y
    rw [heq, hO_nsmul_right, hO_smul_right] at a2
    rw [a1, map_sub, map_one, hcc]
    have : cA D e * (1 - e) = cA D e := by
      rw [mul_sub, mul_one, mul_comm, hec, sub_zero]
    rw [this, mul_assoc, ← a2]
  have k2 : hO S T (c • Y) ((e * incA D ((2 : ℕ) : D.host.E)⁻¹) • Z) =
      (c : AE D) * cA D e * hO S T Y Z * incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    rw [hO_nsmul_left, hO_smul_right, map_mul, hcA2]
    exact comm4 _ _ _ _
  rw [symplOH, symplO, k1, split_half (incA D) (incA D D.host.xi0) ((c : AE D) * cA D e * hO S T Y Z), map_add (f := _),
    half_add (algebraMap D.host.F (AF D.host.F)), ← k2]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hY hZ'

end GlobalTheory.ConjHalfCocycle

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isSBHalf_stepDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Z e hS hT _ _ he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ L.Pg
    (fun y => omegaG L χ y * omegaQ ∅ L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' h,
        GlobalTheory.PlaceDatum.omegaQ_congr ∅ L.r ξ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]

end GlobalTheory.ChainOnto

end
end
