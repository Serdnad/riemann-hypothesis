module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {v : Pl F} (τ : E →ₐ[F] Fv F v)

theorem map_mem_splitLat {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, AddSubgroup.subset_closure ⟨1, one_mem _, z, hz, rfl⟩,
    funext fun i => by simp [splitVec, splitProj_tmul]⟩

theorem splitLat_le {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v)) (hN : ∀ z ∈ L, (fun i => τ (z i)) ∈ N) :
    splitLat τ L ≤ N := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · have := N.smul_mem ⟨a, ha⟩ (hN x hx)
    convert this using 1
    rfl
  · have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    rw [this]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have : splitVec τ (-y) = -splitVec τ y := funext fun _ => map_neg _ _
    rw [this]; exact neg_mem hy

theorem map_mem_of_unit {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {c : E} (hc : c • x ∈ L)
    (hv : Valued.v (τ c) = 1) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    (a • fun i => τ (x i)) ∈ splitLat τ L := by
  have h0 : τ c ≠ 0 := fun e => by simp [e] at hv
  have h1 : a * (τ c)⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem ha (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one])
  have := (splitLat τ L).smul_mem ⟨_, h1⟩ (map_mem_splitLat τ hc)
  convert this using 1
  funext i
  change a * τ (x i) = a * (τ c)⁻¹ * τ (c * x i)
  rw [map_mul]
  field_simp

theorem exists_basis (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ) (hn : n = n₁ + 2) (h01 : i₀ < i₁) (h1n : i₁ < n) (hlat : L.IsFullLattice E)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y)
    (hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1)
    (hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1)
    (hβ₁ : IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁) :
    ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  classical
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := j.2
    unfold skip; split_ifs <;> omega
  let f : Fin n₁ ⊕ Bool → Fin n := Sum.elim (fun j => ⟨skip i₀ i₁ j, hsk j⟩)
    fun b => cond b ⟨i₁, h1n⟩ ⟨i₀, h01.trans h1n⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hn]⟩
    rintro (a | _ | _) (b | _ | _) e <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, cond, Fin.mk.injEq, skip, Sum.inl.injEq, Fin.ext_iff] at e ⊢ <;>
      first | omega | (split_ifs at e <;> omega)
  let e := Equiv.ofBijective f hf
  let c : Fin n₁ ⊕ Bool → Fin n → Fv F v := Sum.elim (fun j r => (ι.map τ * β₁.1) r j)
    fun b => cond b (fun r => τ (y r)) fun r => τ (x r)
  let b : Matrix (Fin n) (Fin n) (Fv F v) := Matrix.of fun r i => c (e.symm i) r
  have hb : ∀ u : Fin n → Fv F v, b *ᵥ u = (u (e (.inr false)) • fun r => τ (x r)) +
      ι.map τ *ᵥ β₁.1 *ᵥ (fun j => u (e (.inl j))) + u (e (.inr true)) • fun r => τ (y r) := fun u => by
    funext r
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, b, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_bool, c, Sum.elim_inl, Sum.elim_inr, cond]
    ring
  have hmv : ∀ u : Fin n₁ → E, (fun i => τ ((ι *ᵥ u) i)) = ι.map τ *ᵥ fun j => τ (u j) := fun u =>
    funext fun i => RingHom.map_mulVec (τ : E →+* Fv F v) ι u i
  have hsurj : ∀ w ∈ splitLat τ L, ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w := by
    let N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) :=
      { carrier := {w | ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w}
        zero_mem' := ⟨0, fun _ => zero_mem _, Matrix.mulVec_zero _⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u + u', fun i => add_mem (hu i) (hu' i), Matrix.mulVec_add _ _ _⟩
        smul_mem' := by
          rintro a _ ⟨u, hu, rfl⟩
          exact ⟨(a : Fv F v) • u, fun i => mul_mem a.2 (hu i), Matrix.mulVec_smul _ _ _⟩ }
    refine fun w hw => splitLat_le τ N (fun z hz => ?_) hw
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hsplit z hz
    have hu' := hβ₁.mem_iff.1 (map_mem_splitLat τ (L := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) hu)
    refine ⟨fun i => Sum.elim ((β₁⁻¹).1 *ᵥ fun j => τ (u j)) (fun b => cond b (τ t) (τ s)) (e.symm i), fun i => ?_, ?_⟩
    · beta_reduce
      rcases e.symm i with j | _ | _
      · exact hu' j
      · exact hx.1 s hs
      · exact hy.1 t ht
    · rw [hb]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond]
      rw [Matrix.mulVec_mulVec _ β₁.1, Units.mul_inv, Matrix.one_mulVec, ← hmv]
      funext r
      simp
  have hunit : IsUnit b := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have h1 : ∀ z : Fin n → E, (fun i => τ (z i)) ∈ LinearMap.range b.mulVecLin := fun z => by
      have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hlat.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨u, -, hu⟩ := hsurj _ (map_mem_splitLat τ hz); exact ⟨u, hu⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha ha'
      | smul a z _ hz => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ (τ a) hz
    intro w
    have : w = ∑ i, w i • fun k => τ ((Pi.single i 1 : Fin n → E) k) := by
      funext k
      simp [Pi.single_apply, apply_ite]
    rw [this]
    exact (Submodule.sum_mem (LinearMap.range b.mulVecLin) fun i _ => Submodule.smul_mem _ _ (h1 _))
  obtain ⟨β, hβ⟩ := hunit
  have col : ∀ k r, β.1 r (e k) = c k r := fun k r => by rw [hβ]; simp [b]
  refine ⟨β, fun i => ⟨fun hi r => ?_, fun hi r => ?_, fun j hi r => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · rw [show i = e (.inr false) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inr true) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inl j) from Fin.ext hi, col]; rfl
  · rw [hβ, hb]
    obtain ⟨s, hs, hs'⟩ := hx.2
    obtain ⟨t, ht, ht'⟩ := hy.2
    refine add_mem (add_mem (map_mem_of_unit τ hs hs' (hu _)) ?_) (map_mem_of_unit τ ht ht' (hu _))
    refine splitLat_le τ ((splitLat τ L).comap ((ι.map τ).mulVecLin.restrictScalars (v.adicCompletionIntegers F)))
      (fun z hz => ?_) ((hβ₁ _).1 fun j => hu _)
    change ι.map τ *ᵥ (fun j => τ (z j)) ∈ splitLat τ L
    rw [← hmv]
    exact map_mem_splitLat τ hz
  · obtain ⟨u', hu', e'⟩ := hsurj _ hu
    rw [← hβ] at e'
    rw [← Matrix.mulVec_injective_iff_isUnit.2 β.isUnit e']
    exact hu'

end PositivityTheory.ThKG.Tow.Pln

end
end

section

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hJ : ∀ i j, σ (J j i) = ε * J i j)
    (a b : Fin n → E) : σ (form σ J a b) = ε * form σ J b a := by
  have hJ' : ∀ i j, σ (J i j) = ε * J j i := fun i j => hJ j i

  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by

  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} {κ : ℂ}
    (hκ : star κ * e ε = κ) (hJ : ∀ i j, σ (J j i) = ε * J i j) : (κ • J.map e)ᴴ = κ • J.map e := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2 e, hJ,
    map_mul]
  rw [← mul_assoc, hκ]

theorem form_sub_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a - b) = form σ J c a - form σ J c b := by
  have : (fun i => σ ((a - b) i)) = (fun i => σ (a i)) - fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_sub, dotProduct_sub]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]

def formL {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun z := form σ J z x
  map_add' a b := form_add_left J a b x
  map_smul' s a := form_smul_left J s a x

def conjInt (σ : E →ₐ[F] E) (o : 𝓞 E) : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) o

end PositivityTheory.ThKG.Tow.Pln

end
end
