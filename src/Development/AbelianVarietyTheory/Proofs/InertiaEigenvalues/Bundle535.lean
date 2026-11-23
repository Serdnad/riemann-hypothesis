module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle121
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (G₁ G₂ : Matrix (Fin r) (Fin r) D.host.E)
    (hG₁ : G₁ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hG₂ : G₂ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _))
    (hL₂ : (L₂ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₂ * h) : Set _)) :
    ∃ γ : GL (Fin r) D.host.E,
      (L₁ : Set (Fin r → D.host.E)) = (γ : Matrix (Fin r) (Fin r) D.host.E).mulVec '' (L₂ : Set _) ∧
      (∀ v w, herm G₁ ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec v) ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec w) =
        herm G₂ v w) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (γ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG₁ hG₂
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
  obtain ⟨ht1, -⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) 1 (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
  rw [hprod] at ht1
  have hmem : ∀ (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V),
      (L : Set (Fin V.rank → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast (rfl : V.rank = V.rank).symm) '' (latG V g : Set _) →
      ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g := fun L g hL v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ L₂ ↔ δ.1 *ᵥ v ∈ L₁ := fun v => by
    rw [hmem _ _ hL₂, hmem _ _ hL₁, ht1, hδf]
  refine ⟨δ, ?_, fun u v => ?_, fun τ θ hθ x => ?_⟩
  · ext v
    constructor
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
  · rw [hG₁, hG₂]
    exact hδu u v
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]



theorem frames_differ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨-, -, -, -, -, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, hL₂, -, hf₂⟩ := hd₂ h
  obtain ⟨γ, hl, hi, hf⟩ := move (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ _).1 (hW₂ _).1 hL₁ hL₂
  refine ⟨γ, hl, hi, fun τ t₂ t₁ => ?_⟩
  have e₂' := hf₂ ⟨τ, t₂⟩
  have e₁' := hf₁ ⟨τ, t₁⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
  rw [e₁', e₂']
  exact hf τ _ (hth₁ _ ⟨τ, t₁⟩) _

end GlobalTheory.CoverFrameMove
end

section

noncomputable section

namespace GlobalTheory.Prism

theorem pi_mem_iff_forall_mem_map_eval {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type}
    [∀ i, CommRing (A i)] (K : Ideal (∀ i, A i)) (y : ∀ i, A i) :
    y ∈ K ↔ ∀ i, y i ∈ K.map (Pi.evalRingHom A i) := by
  refine ⟨fun h i => Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx, hxi⟩ := (Ideal.mem_map_iff_of_surjective _
    (fun b => ⟨Pi.single i b, by simp⟩ : Function.Surjective (Pi.evalRingHom A i))).1 (h i)
  have e : Pi.single i (y i) = Pi.single i 1 * x := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [← hxi]
    · simp [hj]
  rw [e]; exact K.mul_mem_left _ hx

theorem smodEq_smul_top_iff {B : Type} [CommRing B] (K : Ideal B) (x y : B) :
    x ≡ y [SMOD (K • ⊤ : Submodule B B)] ↔ x - y ∈ K := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {q : A}
    (h : Module.Invertible A ↥(Ideal.span {q})) : q ∈ nonZeroDivisors A := by
  have key : ∀ x : A, x * q = 0 → x = 0 := by
    intro x hx
    apply (Module.Invertible.toModuleEnd_bijective A ↥(Ideal.span {q})).1
    ext ⟨m, hm⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    simp
    linear_combination c * hx
  exact mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

def Delta.pi {l : ℕ} {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] (D : ∀ i, Delta l (A i)) :
    Delta l (∀ i, A i) where
  δ a i := (D i).δ (a i)
  δ_one := funext fun i => by simpa using (D i).δ_one
  δ_mul a b := funext fun i => by simpa using (D i).δ_mul (a i) (b i)
  δ_add a b := funext fun i => by simpa [Finset.sum_apply] using (D i).δ_add (a i) (b i)
  φ := RingHom.pi fun i => (D i).φ.comp (Pi.evalRingHom A i)
  φ_eq a := funext fun i => (D i).φ_eq (a i)

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem pi_mem_span_iff (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) (x : ∀ i, (C i).A) :
    x ∈ Ideal.span {t} ↔ ∀ i, x i ∈ (C i).I := by
  classical
  rw [pi_mem_iff_forall_mem_map_eval]
  simp [Ideal.map_span, ht]

theorem pi_mem_nonZeroDivisors (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) : t ∈ nonZeroDivisors (∀ i, (C i).A) := by
  have hz : ∀ i, t i ∈ nonZeroDivisors (C i).A := fun i =>
    mem_nonZeroDivisors_of_invertible_span (ht i ▸ (C i).inv)
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => funext fun i => ?_, fun x hx => funext fun i => ?_⟩
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).1 (x i) (congrFun hx i)
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).2 (x i) (congrFun hx i)

theorem pi_isAdicComplete (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) (∀ i, (C i).A) := by
  classical
  have hJ : ∀ (m : ℕ) (y : ∀ i, (C i).A),
      y ∈ (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) ^ m ↔
        ∀ i, y i ∈ (Ideal.span {((l : ℕ) : (C i).A)} ⊔ (C i).I) ^ m := by
    intro m y
    rw [pi_mem_iff_forall_mem_map_eval]
    simp [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, ht]
  refine { haus' := fun x hx => funext fun i => ?_, prec' := fun f hf => ?_ }
  · refine (C i).complete.toIsHausdorff.haus' (x i) fun n => ?_
    rw [smodEq_smul_top_iff]
    have := (hJ n _).1 ((smodEq_smul_top_iff _ _ _).1 (hx n)) i
    simpa using this
  · choose L hL using fun i => (C i).complete.toIsPrecomplete.prec' (fun n => f n i)
      (fun {m n} hmn => (smodEq_smul_top_iff _ _ _).2 (by
        have := (hJ m _).1 ((smodEq_smul_top_iff _ _ _).1 (hf hmn)) i
        simpa using this))
    exact ⟨fun i => L i, fun n => (smodEq_smul_top_iff _ _ _).2 ((hJ n _).2 fun i => by
      simpa using (smodEq_smul_top_iff _ _ _).1 (hL i n))⟩

theorem pi_l_mem (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ((l : ℕ) : ∀ i, (C i).A) ∈ Ideal.span {t} ⊔ (Ideal.span {t}).map (Delta.pi fun i => (C i).D).φ := by
  have h : ∀ i, ∃ a b : (C i).A, a * t i + b * (C i).D.φ (t i) = (l : (C i).A) := by
    intro i
    have := (C i).l_mem
    rw [ht i, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, e⟩ := this
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, e⟩
  choose a b hab using h
  rw [Submodule.mem_sup]
  refine ⟨a * t, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    b * (Delta.pi fun i => (C i).D).φ t,
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)),
    funext fun i => ?_⟩
  exact hab i

theorem quot_natCast_pow_mul_eq_zero_iff {B : Type} [CommRing B] (K : Ideal B) (l m : ℕ) (a : B) :
    ((l : B ⧸ K)) ^ m * Ideal.Quotient.mk K a = 0 ↔ (l : B) ^ m * a ∈ K := by
  rw [← map_natCast (Ideal.Quotient.mk K), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

theorem pi_bdd (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ∃ N : ℕ, ∀ x : (∀ i, (C i).A) ⧸ Ideal.span {t},
      (∃ m : ℕ, ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ m * x = 0) →
        ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ N * x = 0 := by
  choose n hn using fun i => (C i).bdd
  refine ⟨Finset.univ.sup n, fun x ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quot_natCast_pow_mul_eq_zero_iff, pi_mem_span_iff C t ht] at hm ⊢
  intro i
  have h1 := hn i (Ideal.Quotient.mk _ (a i)) ⟨m, (quot_natCast_pow_mul_eq_zero_iff _ _ _ _).2
    (by simpa using hm i)⟩
  rw [quot_natCast_pow_mul_eq_zero_iff] at h1
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  have e : ((l : ℕ) : ∀ i, (C i).A) ^ Finset.univ.sup n * a =
      ((l : ℕ) : ∀ i, (C i).A) ^ (Finset.univ.sup n - n i) * (((l : ℕ) : ∀ i, (C i).A) ^ n i * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  simpa using Ideal.mul_mem_left _ ((l : (C i).A) ^ (Finset.univ.sup n - n i)) h1

end GlobalTheory.Prism

namespace GlobalTheory.Prism

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

def piQuotMap (C : ι → Obj l R) : (∀ i, (C i).A) →+* ∀ i, (C i).A ⧸ (C i).I :=
  RingHom.pi fun i => (Ideal.Quotient.mk (C i).I).comp (Pi.evalRingHom _ i)

theorem piQuotMap_surjective (C : ι → Obj l R) : Function.Surjective (piQuotMap C) := fun y =>
  ⟨fun i => (Ideal.Quotient.mk_surjective (y i)).choose,
    funext fun i => (Ideal.Quotient.mk_surjective (y i)).choose_spec⟩

theorem piQuotMap_ker (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    RingHom.ker (piQuotMap C) = Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, pi_mem_span_iff C t ht, funext_iff]
  exact forall_congr' fun i => Ideal.Quotient.eq_zero_iff_mem

def piQuotEquiv (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    (∀ i, (C i).A) ⧸ Ideal.span {t} ≃+* ∀ i, (C i).A ⧸ (C i).I :=
  (Ideal.quotEquivOfEq (piQuotMap_ker C t ht).symm).trans
    (RingHom.quotientKerEquivOfSurjective (piQuotMap_surjective C))

theorem piQuotEquiv_mk (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (a : ∀ i, (C i).A) :
    piQuotEquiv C t ht (Ideal.Quotient.mk _ a) = fun i => Ideal.Quotient.mk (C i).I (a i) := rfl

def Obj.pi (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    Obj l R where
  A := ∀ i, (C i).A
  D := Delta.pi fun i => (C i).D
  I := Ideal.span {t}
  inv := invertible_span_singleton (pi_mem_nonZeroDivisors C t ht)
  complete := pi_isAdicComplete C t ht
  l_mem := pi_l_mem C t ht
  bdd := pi_bdd C t ht
  str := (piQuotEquiv C t ht).symm.toRingHom.comp (RingHom.pi fun i => (C i).str)

theorem piQuotEquiv_str (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (r : R) : piQuotEquiv C t ht ((Obj.pi C t ht).str r) = fun i => (C i).str r :=
  (piQuotEquiv C t ht).apply_symm_apply (fun i => (C i).str r)

def Hom.piEval (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (i : ι) : Hom (Obj.pi C t ht) (C i) where
  f := Pi.evalRingHom (fun i => (C i).A) i
  f_δ _ := rfl
  f_I a h := (pi_mem_span_iff C t ht a).1 h i
  f_str r a h := by
    have := congrArg (piQuotEquiv C t ht) h
    exact congrFun ((piQuotEquiv_mk C t ht a).symm.trans (this.trans (piQuotEquiv_str C t ht r))) i

def Hom.piLift (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (Z : Obj l R) (a : ∀ i, Hom Z (C i)) : Hom Z (Obj.pi C t ht) where
  f := RingHom.pi fun i => (a i).f
  f_δ z := funext fun i => (a i).f_δ z
  f_I z hz := (pi_mem_span_iff C t ht _).2 fun i => (a i).f_I z hz
  f_str r z h := (piQuotEquiv C t ht).injective ((piQuotEquiv_mk C t ht _).trans
    ((funext fun i => (a i).f_str r z h).trans (piQuotEquiv_str C t ht r).symm))

end GlobalTheory.Prism

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.Prism.finite_product_oriented : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∃ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) ∧ (∀ x, x ∈ Q.I ↔ ∀ i, (π i).f x ∈ (C i).I) ∧ ∀ (Z : Obj l R) (a : ∀ i, Hom Z (C i)), ∃ c : Hom Z Q, ∀ i, (π i).comp c = a i := by
  intro l _ R _ n C hC
  choose t ht using hC
  exact ⟨Obj.pi C t ht, fun i => Hom.piEval C t ht i,
    ⟨fun x y h => funext fun i => congrFun h i, fun y => ⟨y, rfl⟩⟩,
    fun x => pi_mem_span_iff C t ht x,
    fun Z a => ⟨Hom.piLift C t ht Z a, fun i => Hom.ext' (RingHom.ext fun _ => rfl)⟩⟩
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_pow_succ_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A),
    (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  intro l hl A _ D J hlJ n
  have hl0 : 0 < l := hl.out.pos
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1) := by
      rw [pow_succ' J (n + 1)] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        refine ⟨?_, ?_⟩
        · rw [pow_succ' J (n + 1)]; exact Ideal.mul_mem_mul ha hb
        · rw [D.δ_mul]
          have h1 : a ^ l * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)
          have h2 : b ^ l * D.δ a ∈ J ^ (n + 1) :=
            Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)
          have h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)
          exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨Ideal.add_mem _ hy1 hz1, ?_⟩
        rw [D.δ_add]
        refine Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)
        have hk0 : 0 < k := (Finset.mem_Ioo.1 hk).1
        have hyk : y ^ k ∈ J ^ (n + 1) :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)
    exact key.2

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ProjDescent

section SlopeTestRemainingChoices

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction (h : SemiBC u) (P : N → Prop) (h0 : ∀ x, P (u x)) (h1 : ∀ y z, P y → P z → P (y + z))
    (h2 : ∀ (b : B) y, P y → P (b • y)) (y : N) : P y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

end SlopeTestRemainingChoices

theorem descent : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  intro A B D _ _ _ f p q hpq hf hfix P _ _ _ _ PB _ _ PD _ _ u u₁ u₂ w hu hw h₁ h₂
  classical
  obtain ⟨n, s, g, -, -, hsg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hx : ∀ x, s (g x) = x := fun x => LinearMap.congr_fun hsg x
  set e : Fin n → P := fun i => s (fun j => if i = j then 1 else 0) with he
  have hdec : ∀ c : Fin n → A, u (s c) = ∑ i, f (c i) • u (e i) := by
    intro c

    rw [LinearMap.pi_apply_eq_sum_univ s c, map_sum]
    simp only [LinearMap.map_smulₛₗ, e]
  obtain ⟨WB, hWB, -⟩ := hu (Fin n → B)
    { toFun := fun x i => f (g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  obtain ⟨WD, hWD, -⟩ := hw (Fin n → D)
    { toFun := fun x i => p (f (g x i))
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  have hWB' : ∀ x i, WB (u x) i = f (g x i) := fun x i => congrFun (hWB x) i
  have hWD' : ∀ x i, WD (w x) i = p (f (g x i)) := fun x i => congrFun (hWD x) i
  have hrec : ∀ z, z = ∑ i, WB z i • u (e i) := by
    intro z
    refine induction hu (fun z => z = ∑ i, WB z i • u (e i)) (fun x => ?_) (fun y z hy hz => ?_)
      (fun b y hy => ?_) z
    · conv_lhs => rw [← hx x]
      rw [hdec]; simp only [hWB']
    · conv_lhs => rw [hy, hz]
      simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · conv_lhs => rw [hy]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hp : ∀ z i, p (WB z i) = WD (u₁ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, p (WB z i) = WD (u₁ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₁, hWD', hWB']
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  have hq : ∀ z i, q (WB z i) = WD (u₂ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, q (WB z i) = WD (u₂ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₂, hWD', hWB']
      exact (RingHom.congr_fun hpq (g x i)).symm
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  refine ⟨fun x y hxy => ?_, fun z hz => ?_⟩
  · have hg : g x = g y := funext fun i => hf (by rw [← hWB', ← hWB', hxy])
    rw [← hx x, ← hx y, hg]
  · have hb : ∀ i, ∃ b, f b = WB z i := fun i => RingHom.mem_range.1 (hfix _ (by rw [hp, hq, hz]))
    choose b hb using hb
    exact ⟨s b, by rw [hdec]; simp only [hb]; exact (hrec z).symm⟩

end GlobalTheory.BSP.ProjDescent
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (harm m w B).map (harmFn m w B) = Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  first | exact @GlobalTheory.ExportSeries.Onto.map_harm_eq | exact GlobalTheory.ExportSeries.Onto.map_harm_eq | (intros; apply GlobalTheory.ExportSeries.Onto.map_harm_eq <;> assumption)
end
