module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OverBasis

open Matrix GlobalTheory.HL.SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_comb (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin m → Fin n → E)
    (c : Fin m → E) : (fun a => hf L Hm (∑ b, c b • y b) (y a)) = gramT L Hm y *ᵥ c := by
  funext a
  rw [hf_sum_l]
  simp [gramT, Matrix.mulVec, dotProduct, mul_comm]

theorem linearIndependent_of_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin m → Fin n → E) (h : IsUnit (gramT L Hm y).det) : LinearIndependent E y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 := hf_comb L Hm y c
  rw [hc] at h1
  have h2 : gramT L Hm y *ᵥ c = 0 := by
    rw [← h1]; funext a; simp [hf]
  have h3 : (gramT L Hm y)⁻¹ *ᵥ (gramT L Hm y *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_zero] at h3
  exact fun i => congrFun h3.symm i

omit [TopologicalSpace E] in
theorem sum_smul_rmul {n m : ℕ} (y : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (c : Fin m → E) : ∑ j, c j • rmul y B j = ∑ i, (B *ᵥ c) i • y i := by
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem exists_basis_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (y : Fin m → Fin n → E), IsUnit (gramT L Hm y).det → ∀ Mh : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range y) ≤ Mh → (∀ v ∈ Mh, v ∈ Submodule.span E (Set.range y)) → (∀ v ∈ Mh, ∀ w ∈ Mh, hf L Hm v w ∈ L.O) → LinearIndependent E y ∧ ∃ A : Matrix (Fin m) (Fin m) E, IsIntM L A ∧ IsUnit A.det ∧ Mh = Submodule.span L.O (Set.range (rmul y A⁻¹)) ∧ LinearIndependent E (rmul y A⁻¹) ∧ rmul (rmul y A⁻¹) A = y := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ m y hG Mh hy hsp hint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  have hli := linearIndependent_of_gram L Hm y hG
  refine ⟨hli, ?_⟩
  have hyM : ∀ a, y a ∈ Mh := fun a => hy (Submodule.subset_span ⟨a, rfl⟩)
  let f : (Fin m → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun w => ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => (w a : E)) i • y i
      map_add' := fun v w => by
        have : (fun a => ((v + w) a : E)) = (fun a => (v a : E)) + fun a => (w a : E) := rfl
        rw [this, Matrix.mulVec_add]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have : (fun a => ((c • v) a : E)) = (c : E) • fun a => (v a : E) := rfl
        rw [this, Matrix.mulVec_smul, RingHom.id_apply, Subring.smul_def, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_assoc] }
  have hle : Mh ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hsp v hv)
    refine ⟨fun a => ⟨_, hint _ hv _ (hyM a)⟩, ?_⟩
    show ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => hf L Hm (∑ b, c b • y b) (y a)) i • y i = _
    rw [hf_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := exists_eq_span_range m (Mh.comap f)
  let B : Matrix (Fin m) (Fin m) E :=
    Matrix.of fun i j => ((gramT L Hm y)⁻¹ *ᵥ fun a => (b j a : E)) i
  have hM : Mh = Submodule.span L.O (Set.range (rmul y B)) := by
    rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
    rfl
  have hA : ∀ j, ∃ c : Fin m → L.O, ∑ i, c i • rmul y B i = y j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun L.O).1 (hM ▸ hyM j)
  choose c hc using hA
  let A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => (c j i : E)
  have hA : rmul (rmul y B) A = y := funext hc
  have hBA : B * A = 1 := by
    ext i j
    have h1 : ∑ i, (B *ᵥ fun k => A k j) i • y i = y j := by
      rw [← sum_smul_rmul]; exact hc j
    have h2 : ∑ i, ((B *ᵥ fun k => A k j) - (Pi.single j 1 : Fin m → E)) i • y i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1]
      simp [Pi.single_apply]
    have h3 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 i)
    rw [Matrix.one_apply, ← Pi.single_apply, ← h3]
    rfl
  have hinv : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  refine ⟨A, fun i j => (c j i).2, Matrix.isUnit_det_of_left_inverse hBA, ?_⟩
  rw [hinv]
  refine ⟨hM, ?_, hA⟩
  rw [Fintype.linearIndependent_iff]
  intro d hd
  rw [sum_smul_rmul] at hd
  have h1 : B *ᵥ d = 0 := funext (Fintype.linearIndependent_iff.1 hli _ hd)
  have h2 : A *ᵥ (B *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hBA, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact fun i => congrFun h2.symm i

end GlobalTheory.HL.OverBasis
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres : ∀ (G α β : Type) [Group G] [MulAction G α] [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) → Stable G X → Stable G Y → Set.MapsTo π X Y → (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) → orbMass G X = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  first | exact @GlobalTheory.Mass.orbMass_eq_orbSum_fibre | exact GlobalTheory.Mass.orbMass_eq_orbSum_fibre | (intros; apply GlobalTheory.Mass.orbMass_eq_orbSum_fibre <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMove

section

variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem discN_congr {V W : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (k : W →ₗ⋆[K] W →ₗ[K] K) (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (A : Submodule R V) (B : Submodule R W)
    (hAB : ∀ x, e x ∈ B ↔ x ∈ A) : discN k B = discN h A := by
  have hd : ∀ x, e x ∈ dual k B ↔ x ∈ dual h A := by
    intro x
    unfold dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    constructor
    · intro H y hy
      rw [← he]
      exact H _ ((hAB y).2 hy)
    · intro H y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [he]
      exact H _ ((hAB z).1 hy)
  have hm : ∀ (A : Submodule R V) (B : Submodule R W), (∀ x, e x ∈ B ↔ x ∈ A) →
      B.toAddSubgroup = A.toAddSubgroup.map (e : V →+ W) := by
    intro A B H
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · intro hy
      exact ⟨z, (H z).1 hy, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : e w = e z := hwz
      rw [← this]
      exact (H w).2 hw
  unfold discN idxN
  rw [hm A B hAB, hm _ _ hd]
  exact AddSubgroup.relIndex_map_map_of_injective (f := (e : V →+ W)) _ _ e.injective

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem smul_mem_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V) (x : V) :
    (g : V ≃ₗ[K] V) x ∈ g • L ↔ x ∈ L := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have : w = x := (g : V ≃ₗ[K] V).injective hwx
    exact this ▸ hw
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem smul_mem_primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V)
    (U : Submodule K V) (j n : ℕ) : g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n := by
  let e : U ≃ₗ[K] (g • U : Submodule K V) := (g : V ≃ₗ[K] V).submoduleMap U
  have he : ∀ x : U, (e x : V) = (g : V ≃ₗ[K] V) x := fun _ => rfl
  have h1 : Module.finrank K (g • U : Submodule K V) = Module.finrank K U := e.finrank_eq.symm
  have h2 : discN (hRes h (g • U)) (latIn (g • U) (g • L)) = discN (hRes h U) (latIn U L) := by
    refine discN_congr _ _ e (fun x y => ?_) _ _ (fun x => ?_)
    · exact g.2 (x : V) (y : V)
    · exact smul_mem_smul_iff h g L (x : V)
  change _ ∧ _ ↔ _ ∧ _
  rw [h1, h2]

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ g L U j n
  refine ⟨smul_mem_primSp h g L U j n, ?_⟩
  have hi : primSp h (g • L) j n = (fun W : Submodule K V => g • W) '' primSp h L j n := by
    ext W
    constructor
    · intro hW
      refine ⟨g⁻¹ • W, ?_, smul_inv_smul g W⟩
      rw [← smul_mem_primSp h g, smul_inv_smul]
      exact hW
    · rintro ⟨W', hW', rfl⟩
      exact (smul_mem_primSp h g L W' j n).2 hW'
  rw [hi]
  exact (MulAction.injective g).encard_image _

end GlobalTheory.Mass.PrimMove
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

def pos (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def Dep (k r d : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j, pos k r j < pos k r i + d → X i j = 0

abbrev UTr (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev Bk (r : ℕ) : Type := UTr r ⊕ Fin r ⊕ UTr r ⊕ Fin r

def VM (k r : ℕ) : Bk r → Type
  | .inl _ => ℂ
  | .inr (.inl _) => Fin (k + 1) → ℂ
  | .inr (.inr (.inl _)) => ℂ
  | .inr (.inr (.inr _)) => ℝ

instance instVM (k r : ℕ) : ∀ β, AddCommGroup (VM k r β)
  | .inl _ => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inl _) => inferInstanceAs (AddCommGroup (Fin (k + 1) → ℂ))
  | .inr (.inr (.inl _)) => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inr (.inr _)) => inferInstanceAs (AddCommGroup ℝ)

def cM (k r : ℕ) : ∀ β : Bk r, Mt k r → VM k r β
  | .inl p, x => x (eI k r p.1.1) (eI k r p.1.2)
  | .inr (.inl a), x => fun j => x (eI k r a) (wI k r j)
  | .inr (.inr (.inl p)), x => x (eI k r p.1.1) (esI k r p.1.2)
  | .inr (.inr (.inr a)), x => (x (eI k r a) (esI k r a)).im

def degB (r : ℕ) : Bk r → ℕ
  | .inl p => p.1.2.val - p.1.1.val
  | .inr (.inl a) => r - a.val
  | .inr (.inr (.inl p)) => 2 * r - p.1.1.val - p.1.2.val
  | .inr (.inr (.inr a)) => 2 * r - 2 * a.val

section Glob

variable {E : Type} [Field E] [NumberField E]

def gM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (w : InfinitePlace E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  A w * γ.map w.embedding * (A w)⁻¹

def actM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (x : InfinitePlace E → Mt k r) :
    InfinitePlace E → Mt k r :=
  fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))

def GN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {γ | InN σ J P γ ∧ latMap γ Λ = Λ}

def ideLat (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℂ) where
  carrier := {z | ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, fun w => by simp [h]⟩

def skewLat (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℝ) where
  carrier := {z | ∃ y ∈ I, σ y = -y ∧ ∀ w, z w = c * (w.embedding y).im}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, hs, h⟩ ⟨y', hy', hs', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', by simp [hs, hs']; ring, fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, hs, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, by simp [hs], fun w => by simp [h]⟩

def midLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (I : FractionalIdeal (𝓞 E)⁰ E) :
    Set (Fin (2 * r + k + 1) → E) :=
  {t | (∀ a : Fin r, form σ J t (fun i => P i a.castSucc) = 0 ∧ form σ J t (fun i => f i a) = 0) ∧
    ∀ c ∈ I⁻¹, c • t ∈ Λ}

def homLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : Set (InfinitePlace E → Fin (k + 1) → ℂ) :=
  {z | ∃ t ∈ midLat σ J Λ P f I, ∀ w l,
    z w l = (c : ℂ) * herm (Hpk k r) (bvec (wI k r l)) ((A w).mulVec fun i => w.embedding (t i))}

end Glob

section Bundle

variable {E : Type} [Field E] [NumberField E]

def HasDom {V : Type} [AddCommGroup V] [MeasurableSpace V] (μ : Measure V) (L : Set V) (c : ℝ≥0∞) : Prop :=
  ∃ D : Set V, MeasurableSet D ∧ (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) ∧ μ D = c

def blkSet (ι : Type) (k r : ℕ) (SU : UTr r → Set (ι → ℂ)) (SH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (SC : UTr r → Set (ι → ℂ)) (SG : Fin r → Set (ι → ℝ)) : ∀ β : Bk r, Set (ι → VM k r β)
  | .inl p => SU p
  | .inr (.inl a) => SH a
  | .inr (.inr (.inl p)) => SC p
  | .inr (.inr (.inr a)) => SG a

def IsVolData {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E) {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
    GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ ∧ IsFrame (σ : E →+* E) J (algebraMap F E T) P ∧
    IsDual (σ : E →+* E) J P f ∧ tupLat (id1 E r) (sideM P f) ≤ Λ ∧ IsModelAt J A ∧ (∀ a, 0 < s a) ∧
    Adapted A P f s

def rowE (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e y : Fin n → E) (t : E) : Matrix (Fin n) (Fin n) E :=
  fun i j => (if i = j then 1 else 0) + (y i + t * e i) * Matrix.vecMul (fun l => σ (e l)) J j -
    e i * Matrix.vecMul (fun l => σ (y l)) J j

end Bundle

end GlobalTheory.SnMass.VolN
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MoveFibre

theorem cint_coset {W : Type} [AddCommGroup W] (A : AddSubgroup W) (P : W → Prop) (t₀ : W)
    (hP : ∀ t, P t ↔ t - t₀ ∈ A) : cint A (ind P) = 1 := by
  have hN : Nice A (ind P) := by
    refine ⟨A, le_rfl, by simp, fun w b hb => ?_, ?_⟩
    · have : P (w + b) ↔ P w := by
        rw [hP, hP, show w + b - t₀ = w - t₀ + b by abel]
        exact A.add_mem_cancel_right hb
      simp only [ind, this]
    · refine (Set.finite_singleton (QuotientAddGroup.mk t₀ : W ⧸ A)).subset ?_
      rintro _ ⟨w, hw, rfl⟩
      have h1 : P w := by
        by_contra h
        exact hw (by simp [ind, h])
      rw [Set.mem_singleton_iff, eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
      exact (hP w).1 h1
  rw [cint, dite_eq_left hN]
  obtain ⟨hle, hidx, -, -⟩ := hN.choose_spec
  generalize hN.choose = B at hle hidx
  let g : A ⧸ B.addSubgroupOf A → W ⧸ B := fun x =>
    Quotient.liftOn' x (fun a : A => (QuotientAddGroup.mk (t₀ + a) : W ⧸ B)) (fun a b hab => by
      rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hab
      rw [QuotientAddGroup.eq]
      convert hab using 1
      push_cast; abel)
  have hg : ∀ a : A, g (QuotientAddGroup.mk a) = QuotientAddGroup.mk (t₀ + a) := fun _ => rfl
  have hinj : Function.Injective g := by
    intro x y
    induction x using QuotientAddGroup.induction_on with | H a => ?_
    induction y using QuotientAddGroup.induction_on with | H b => ?_
    intro h
    rw [hg, hg, QuotientAddGroup.eq] at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    convert h using 1
    push_cast; abel
  have hr : ∀ c : W ⧸ B, P c.out ↔ c ∈ Set.range g := by
    intro c
    rw [hP]
    constructor
    · intro h
      exact ⟨QuotientAddGroup.mk ⟨_, h⟩, by rw [hg]; simp⟩
    · rintro ⟨x, hx⟩
      induction x using QuotientAddGroup.induction_on with | H a => ?_
      rw [hg, ← c.out_eq, QuotientAddGroup.eq] at hx
      have := A.add_mem (hle hx) a.2
      convert this using 1
      abel
  have hfin : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hidx
  have := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  have hs : (∑ᶠ c : W ⧸ B, ind P c.out) = ∑ᶠ c ∈ Set.range g, (1 : ℂ) := by
    refine finsum_congr fun c => ?_
    rw [finsum_eq_if]
    simp only [ind, hr]
  rw [hs, finsum_mem_range hinj, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  exact div_self (Nat.cast_ne_zero.2 hidx)

theorem cj_hf_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (u : Fin n → E) :
    L.cj (hf L Hm u u) = hf L Hm u u := by
  have h1 : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i

  simp only [hf, map_sum, map_mul, L.cj_cj, h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fibre_scalar : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ u
  obtain ⟨htr, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hfix : L.cj (S.h u u) = S.h u u := cj_hf_self L S.herm.1 u
  have h2 : algebraMap F E 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hT : ∀ t, t ∈ S.refT ↔ t + L.cj t = 0 ∧
      ∃ c ∈ L.O, algebraMap F E ((S.ϖ : F) ^ S.a) * c = t := fun t => Iff.rfl
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx, hxc⟩ := htr c
    rw [map_mul, ← hxc] at hc
    refine cint_coset _ _
      (algebraMap F E ((S.ϖ : F) ^ S.a) * x - algebraMap F E 2⁻¹ * S.h u u) fun t => ?_
    rw [hT]
    simp only [map_sub L.cj, map_mul L.cj, AlgEquiv.commutes, hfix]
    constructor
    · rintro ⟨⟨y, hy, e⟩, ht⟩
      exact ⟨by linear_combination ht + hc + S.h u u * h2,
        y - x, L.O.sub_mem hy hx, by linear_combination -e⟩
    · rintro ⟨ht, y, hy, e⟩
      exact ⟨⟨y + x, L.O.add_mem hy hx, by linear_combination -e⟩,
        by linear_combination ht - hc - S.h u u * h2⟩
  · rintro ⟨t, ⟨y, hy, e⟩, ht⟩
    obtain ⟨c, hc⟩ := (hO y hy).2.1
    refine ⟨c, ?_⟩
    have e' := congrArg L.cj e
    simp only [map_add L.cj, map_mul L.cj, AlgEquiv.commutes, hfix] at e'
    rw [map_mul, ← hc]
    linear_combination e + e' - ht - S.h u u * h2

end GlobalTheory.MoveFibre
end
