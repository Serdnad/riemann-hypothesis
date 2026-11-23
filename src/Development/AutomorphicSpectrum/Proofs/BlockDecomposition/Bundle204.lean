module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle051
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle198
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Aff

universe u w

section Algebra

variable {R : Type} [CommRing R]

theorem tensor_sub_left (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have key : ∀ z : M ⊗[R] N, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem tensor_sub_right (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  _root_.UpperTheory.Reformulated.B.Qn17.tensor_sub_right M N

variable {I A : Type} [DecidableEq I] [Fintype A] [DecidableEq A] (M : I → Type u) [∀ t, AddCommMonoid (M t)]
  [∀ t, Module R (M t)] (ι : A → I)

theorem component_lof_ne {i j : I} (h : j ≠ i) (x : M i) : DirectSum.component R I M j (DirectSum.lof R I M i x) = 0 := by
  rw [DirectSum.component.of]
  simp [h.symm]

def sumPi (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) :
    (⨁ t, M t) ≃ₗ[R] ∀ a, M (ι a) :=
  LinearEquiv.ofLinear (LinearMap.pi fun a => DirectSum.component R I M (ι a))
    (∑ a, (DirectSum.lof R I M (ι a)).comp (LinearMap.proj a))
    (by
      refine LinearMap.ext fun f => funext fun b => ?_

      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply, map_sum]
      rw [Finset.sum_eq_single b]
      · exact DirectSum.component.lof_self R _ _
      · intro a _ hab
        exact component_lof_ne M (fun e => hab (hι e).symm) _
      · intro h
        exact absurd (Finset.mem_univ b) h)
    (by
      refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun x => ?_
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := ht
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
        rw [Finset.sum_eq_single b]
        · rw [DirectSum.component.lof_self]
        · intro a _ hab
          rw [component_lof_ne M (fun e => hab (hι e)) x, map_zero]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · have := hz t ht
        rw [Subsingleton.elim x 0, map_zero, map_zero])

theorem sumPi_lof (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) (b : A) (x : M (ι b)) :
    sumPi (R := R) M ι hι hz (DirectSum.lof R I M (ι b) x) = Pi.single b x := by
  refine funext fun a => ?_
  change DirectSum.component R I M (ι a) (DirectSum.lof R I M (ι b) x) = _
  by_cases h : a = b
  · subst h
    rw [DirectSum.component.lof_self, Pi.single_eq_same]
  · rw [component_lof_ne M (fun e => h (hι e)) x, Pi.single_eq_of_ne h]

end Algebra

variable {K : Type} [Field K]

def diag (c : ℕ) (a : Fin (c + 1)) : Idx c c :=
  ⟨a, a, c - a, c - a, by omega, by omega⟩

theorem diag_inj (c : ℕ) : Function.Injective (diag c) := by
  intro a b h
  exact Fin.ext (congrArg Idx.a h)

theorem kunE_of_diag {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c))
    (hP : ∀ a j, j ≠ a → Subsingleton ((P a).H j)) (hQ : ∀ a j, j ≠ a → Subsingleton ((Q a).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((T a).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((P a).H a) ((Q (c - a)).H (c - a))) ≃ₗ[K] (T c).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (P a).X a) (y : (Q (c - a)).X (c - a))
        (hx : (P a).d a x = 0) (hy : (Q (c - a)).d (c - a) y = 0) (hz : (T c).d c ((pr hc).μ hc x y) = 0),
        e (Pi.single a ((P a).cls x hx ⊗ₜ (Q (c - a)).cls y hy)) = (T c).cls ((pr hc).μ hc x y) hz) :
    KunE pr := by
  intro c n
  have offL : ∀ t : Idx c n, t.i ≠ t.a → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hP t.a t.i h
    exact tensor_sub_left _ _
  have offR : ∀ t : Idx c n, t.j ≠ t.a' → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hQ t.a' t.j h
    exact tensor_sub_right _ _
  by_cases hn : n = c
  · subst hn
    obtain ⟨e, he⟩ := hE n
    have hz : ∀ t, t ∉ Set.range (diag n) → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t ht => by
      refine offL t fun hi => ht ?_
      obtain ⟨a, i, a', j, ha, h⟩ := t
      simp only at hi
      subst hi
      obtain rfl : j = a' := by omega
      obtain rfl : j = n - i := by omega
      exact ⟨⟨i, by omega⟩, rfl⟩
    refine ⟨(sumPi (R := K) (fun t : Idx n n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) (diag n) (diag_inj n) hz).trans e, ?_⟩
    intro t x y hx hy hw
    by_cases ht : t ∈ Set.range (diag n)
    · obtain ⟨b, rfl⟩ := ht
      rw [LinearEquiv.trans_apply, sumPi_lof]
      exact he b (by omega) x y hx hy hw
    · have := hz t ht
      have hi : t.i ≠ t.a := fun hi => ht (by
        obtain ⟨a, i, a', j, ha, h⟩ := t
        simp only at hi
        subst hi
        obtain rfl : j = a' := by omega
        obtain rfl : j = n - i := by omega
        exact ⟨⟨i, by omega⟩, rfl⟩)
      have hB : x ∈ (P t.a).B t.i := by
        have := hP t.a t.i hi
        exact ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 x hx).1 (Subsingleton.elim _ _)
      set_option synthInstance.maxHeartbeats 200000 in
        rw [Subsingleton.elim ((P t.a).cls x hx ⊗ₜ[K] (Q t.a').cls y hy) 0, map_zero, map_zero]
      exact (((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hw).2 (CrystallineSemistableComparison.Auxff.memB_left (pr t.ha) t.h x hB y hy)).symm
  · have : Subsingleton ((T c).H n) := hT c n hn
    have hs : ∀ t : Idx c n, Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t => by
      by_cases hi : t.i = t.a
      · refine offR t fun hj => hn ?_
        have := t.ha
        have := t.h
        omega
      · exact offL t hi
    have : Subsingleton (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) := inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem xd_kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (hP : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₁.ι ⋙ E.F₁ a)).H j))
    (hQ : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₂.ι ⋙ E.F₂ a)).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₃.ι ⋙ E.F₃ a)).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((CH.cx (U₁.ι ⋙ E.F₁ a)).H a) ((CH.cx (U₂.ι ⋙ E.F₂ (c - a))).H (c - a))) ≃ₗ[K] (CH.cx (U₃.ι ⋙ E.F₃ c)).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (CH.cx (U₁.ι ⋙ E.F₁ a)).X a) (y : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).X (c - a))
        (hx : (CH.cx (U₁.ι ⋙ E.F₁ a)).d a x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).d (c - a) y = 0)
        (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d c ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) = 0),
        e (Pi.single a ((CH.cx (U₁.ι ⋙ E.F₁ a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).cls y hy)) =
          (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) hz) :
    E.Kun U₁ U₂ U₃ h₁ h₂ :=
  kunE_of_diag (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) hP hQ hT hE

theorem cls_eq {R : Type} [CommRing R] (L : Cx.{w} R) {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0) (hy : L.d n y = 0) :
    L.cls x hx = L.cls y hy := by
  subst e
  rfl

section
variable {X X' P : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q)

theorem hodge_pr_eq (U₁ : ObjectProperty (Thick (smFun X q))) (U₂ : ObjectProperty (Thick (smFun X' q')))
    (U₃ : ObjectProperty (Thick (smFun P (p₁ ≫ q))))
    (h₁ : ∀ T, U₃ T → U₁ ((smS p₁ rfl).G.obj T)) (h₂ : ∀ T, U₃ T → U₂ ((smS p₂ hw).G.obj T)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : CH.Cn (U₁.ι ⋙ G q a) i) (y : CH.Cn (U₂.ι ⋙ G q' a') j) :
    ((hodgeXD q q' p₁ p₂ hw).pr U₁ U₂ U₃ h₁ h₂ ha).μ h x y =
      cupU (p₁ ≫ q) U₃ ha h ((morV p₁ rfl a h₁).pullC i x) ((morV p₂ hw a' h₂).pullC j y) := rfl

end



theorem kun_aff : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂  := by
  intro _ hA hK K _ _ X X' P q q' p₁ p₂ hP V V' d d' hc hc' h₁ h₂
  obtain ⟨hZ, hE⟩ := hK K X X' P q q' p₁ p₂ hP V V' d d' hc hc'
  refine xd_kun (hodgeXD q q' p₁ p₂ hP.w.symm) _ _ _ h₁ h₂ ?_ ?_ ?_ ?_
  · exact fun a j hj => (hA K X q V d hc a).1 j hj
  · exact fun a j hj => (hA K X' q' V' d' hc' a).1 j hj
  · exact fun a j hj => (hA K P (p₁ ≫ q) _ (d + d') hZ a).1 j hj
  · intro c
    obtain ⟨e, he⟩ := hE c h₁ h₂
    refine ⟨e, fun a hc x y hx hy hz => ?_⟩
    have eq := hodge_pr_eq q q' p₁ p₂ hP.w.symm (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ hc hc x y
    have hz' : (CH.cx ((inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')).ι ⋙ G (p₁ ≫ q) c)).d c (cupU (p₁ ≫ q) _ hc hc ((morV p₁ rfl a h₁).pullC a x) ((morV p₂ hP.w.symm (c - a) h₂).pullC (c - a) y)) = 0 := by
      rw [← eq]
      exact hz
    exact (he a hc x y hx hy hz').trans (cls_eq _ eq.symm _ _)

end GlobalTheory.CompanionTheory.KunGlue.Aff
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ContFn

theorem smod_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    SModEq ((Ideal.span {a}) ^ n • ⊤ : Submodule R R) x y ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) {Γ : Type} [TopologicalSpace Γ]

theorem pi_nzd : A.pi ∈ nonZeroDivisors A.A := A.tf

theorem mem_contR_iff (f : Γ → A.A) :
    f ∈ A.contR Γ ↔ ∀ k : ℕ, ∀ γ : Γ, ∀ᶠ γ' in nhds γ, A.pi ^ k ∣ f γ' - f γ := by
  refine forall_congr' fun k => ?_
  change IsLocallyConstant (fun γ => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (f γ)) ↔ _
  rw [IsLocallyConstant.iff_eventually_eq]
  refine forall_congr' fun γ => Filter.eventually_congr (Filter.Eventually.of_forall fun γ' => ?_)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem pow_cancel {k j : ℕ} {a : A.A} (h : A.pi ^ (k + j) ∣ A.pi ^ k * a) : A.pi ^ j ∣ a := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hk : A.pi ^ k ∈ nonZeroDivisors A.A := pow_mem (pi_nzd A) k
  have := mem_nonZeroDivisors_iff_left.1 hk (a - A.pi ^ j * c) (by rw [mul_sub, hc, pow_add]; ring)
  exact sub_eq_zero.1 this

theorem frob_dvd {k : ℕ} {d : A.A} (h : A.pi ^ (l * k) ∣ A.frob d) : A.pi ^ k ∣ d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', rfl⟩ := A.frob_bijective.2 c
  refine ⟨c', A.frob_bijective.1 ?_⟩
  rw [hc, map_mul]
  congr 1
  change A.pi ^ (l * k) = (A.pi ^ k) ^ l
  rw [← pow_mul, mul_comm]

theorem val_pow_apply (f : A.contR Γ) (k : ℕ) (γ : Γ) : (f ^ k).1 γ = f.1 γ ^ k := by
  simp

theorem dvd_iff (k : ℕ) (f : A.contR Γ) : A.contC Γ A.pi ^ k ∣ f ↔ ∀ γ, A.pi ^ k ∣ f.1 γ := by
  constructor
  · rintro ⟨g, rfl⟩ γ
    refine ⟨g.1 γ, ?_⟩
    change (A.contC Γ A.pi ^ k).1 γ * g.1 γ = _
    rw [val_pow_apply]
    rfl
  · intro h
    choose g hg using h
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun j γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (k + j) γ] with γ' hγ'
      rw [hg γ', hg γ, ← mul_sub] at hγ'
      exact pow_cancel A hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    refine (hg γ).trans ?_
    change _ = (A.contC Γ A.pi ^ k).1 γ * g γ
    rw [val_pow_apply]
    rfl

theorem perfect : PerfectRing (A.contR Γ) l := by
  refine ⟨⟨fun x y h => ?_, fun f => ?_⟩⟩
  · refine Subtype.ext (funext fun γ => A.frob_bijective.1 ?_)
    have e := congrFun (congrArg Subtype.val h) γ
    change (x ^ l).1 γ = (y ^ l).1 γ at e
    rw [val_pow_apply, val_pow_apply] at e
    exact e
  · choose g hg using fun γ => A.frob_bijective.2 (f.1 γ)
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun k γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (l * k) γ] with γ' hγ'
      refine frob_dvd A ?_
      rw [map_sub, hg γ', hg γ]
      exact hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    change ((⟨g, hg'⟩ : A.contR Γ) ^ l).1 γ = _
    rw [val_pow_apply]
    exact hg γ

theorem complete : IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := by
  have hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have h1 : IsHausdorff (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun x hx => by
    refine Subtype.ext (funext fun γ => ?_)
    refine hc.toIsHausdorff.haus' (x.1 γ) fun n => (smod_iff _ _ _ _).2 ?_
    have := (dvd_iff A n x).1 (by simpa using (smod_iff _ _ _ _).1 (hx n)) γ
    simpa using this⟩
  have h2 : IsPrecomplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun f hf => by
    have hp : ∀ m n, m ≤ n → ∀ γ, A.pi ^ m ∣ (f m).1 γ - (f n).1 γ := fun m n h γ =>
      (dvd_iff A m (f m - f n)).1 ((smod_iff _ _ _ _).1 (hf h)) γ
    choose L hL using fun γ => hc.toIsPrecomplete.prec (f := fun n => (f n).1 γ)
      fun {m n} h => (smod_iff _ _ _ _).2 (hp m n h γ)
    have hL' : ∀ n γ, A.pi ^ n ∣ (f n).1 γ - L γ := fun n γ => (smod_iff _ _ _ _).1 (hL γ n)
    have hLm : L ∈ A.contR Γ := (mem_contR_iff A L).2 fun k γ => by
      filter_upwards [(mem_contR_iff A (f k).1).1 (f k).2 k γ] with γ' h
      have e : L γ' - L γ = ((f k).1 γ' - (f k).1 γ) - ((f k).1 γ' - L γ') + ((f k).1 γ - L γ) := by ring
      rw [e]
      exact dvd_add (dvd_sub h (hL' k γ')) (hL' k γ)
    exact ⟨⟨L, hLm⟩, fun n => (smod_iff _ _ _ _).2 ((dvd_iff A n _).2 fun γ => hL' n γ)⟩⟩
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

theorem contC_pi_nzd : A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) :=
  mem_nonZeroDivisors_iff_left.2 fun x hx => Subtype.ext (funext fun γ =>
    mem_nonZeroDivisors_iff_left.1 (pi_nzd A) (x.1 γ) (congrFun (congrArg Subtype.val hx) γ))

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ],
    PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧
      A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧
      ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔
        ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := fun A Γ _ =>
  ⟨perfect A, complete A, contC_pi_nzd A, fun k f => by
    simp only [Ideal.mem_span_singleton]
    exact dvd_iff A k f⟩

end GlobalTheory.CompanionTheory.ContFn
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.UntiltRegular

variable {W R : Type*} [CommRing W] [CommRing R]

theorem mem_span_of_mul_mem_of_hom {l xi : W} (φ : W →+* R)
    (hmem : ∀ y, y ∈ Ideal.span {l} ↔ φ y = 0) (hxi : φ xi ∈ nonZeroDivisors R) (y : W)
    (h : xi * y ∈ Ideal.span {l}) : y ∈ Ideal.span {l} := by
  rw [hmem] at h ⊢
  rw [map_mul] at h
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hxi).mp h

private theorem eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' {l : W} (hl : ∀ x, l * x = 0 → x = 0) (m : ℕ) :
    ∀ t : W, l ^ m * t = 0 → t = 0 := by
  induction m with
  | zero => intro t ht; simpa using ht
  | succ m ihm =>
    intro t ht
    rw [pow_succ, mul_assoc] at ht
    exact hl t (ihm _ ht)

theorem mem_span_pow_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (n : ℕ) :
    ∀ x, xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hx' : xi * x ∈ Ideal.span {l ^ n} := by
      rw [Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow l (Nat.le_succ n)).trans hx
    have h1 := ih x hx'
    rw [Ideal.mem_span_singleton] at h1 hx ⊢
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, hd⟩ := hx
    have h2 : xi * c = l * d := by
      have h0 : l ^ n * (xi * c - l * d) = 0 := by linear_combination hd
      exact sub_eq_zero.mp (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' hl n _ h0)
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨d, h2⟩))
    exact ⟨e, by ring⟩

theorem eq_zero_of_mul_eq_zero {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W) (h : xi * y = 0) :
    y = 0 := by
  have hall : ∀ n, y ∈ Ideal.span {l ^ n} :=
    fun n => mem_span_pow_of_mul_mem hl key n y (by rw [h]; exact zero_mem _)
  apply hH.haus y
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hall n

theorem mem_span_xi_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W)
    (h : l * y ∈ Ideal.span {xi}) : y ∈ Ideal.span {xi} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨y, hc.symm⟩))
  refine ⟨d, sub_eq_zero.mp (hl _ ?_)⟩
  linear_combination hc

theorem regular_of_key {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) :
    Ideal.Quotient.mk (Ideal.span {xi}) l ∈ nonZeroDivisors (W ⧸ Ideal.span {xi}) ∧
      xi ∈ nonZeroDivisors W ∧
      ∀ (n : ℕ) (x : W), xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  refine ⟨?_, ?_, mem_span_pow_of_mul_mem hl key⟩
  · rw [mem_nonZeroDivisors_iff]
    have hq : ∀ x : W ⧸ Ideal.span {xi}, x * Ideal.Quotient.mk (Ideal.span {xi}) l = 0 → x = 0 := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_xi_of_mul_mem hl key x (by rw [mul_comm]; exact hx)
    exact ⟨fun x hx => hq x (by rw [mul_comm]; exact hx), hq⟩
  · rw [mem_nonZeroDivisors_iff]
    have hw : ∀ x : W, xi * x = 0 → x = 0 := fun x hx => eq_zero_of_mul_eq_zero hl hH key x hx
    exact ⟨hw, fun x hx => hw x (by rw [mul_comm]; exact hx)⟩

theorem key {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : A.W)
    (h : A.xi * y ∈ Ideal.span {(l : A.W)}) : y ∈ Ideal.span {(l : A.W)} := by
  refine mem_span_of_mul_mem_of_hom (WittVector.constantCoeff : A.W →+* A.A) (fun x => ?_) ?_ y h
  · rw [A.mem_span_l_iff x]
    exact Iff.rfl
  · have hc : (WittVector.constantCoeff : A.W →+* A.A) A.xi = -A.pi := A.xi_coeff_zero
    have hpi : A.pi ∈ nonZeroDivisors A.A := A.tf
    rw [hc, ← neg_one_mul]
    exact mul_mem isUnit_one.neg.mem_nonZeroDivisors hpi

theorem untilt_regular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧
      ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} →
        x ∈ Ideal.span {(l : A.W) ^ n} := by
  intro l _ A
  have hreg := regular_of_key (W := A.W) (l := (l : A.W)) (xi := A.xi)
    (fun x hx => A.l_mul_eq_zero hx) inferInstance (fun y hy => key A y hy)
  refine ⟨?_, hreg.2.1, hreg.2.2⟩
  have h1 := hreg.1
  rw [map_natCast] at h1
  exact h1

end GlobalTheory.CompanionTheory.UntiltRegular
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.isolate_representation_at_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], IsolateAt F ι := by
  first | exact @GlobalTheory.CompanionTheory.Isolate.isolateAt | exact GlobalTheory.CompanionTheory.Isolate.isolateAt | (intros; apply GlobalTheory.CompanionTheory.Isolate.isolateAt <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.one_vector_formula_of_parts : Prop1 → Simil → Hasse → Cnt → E1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | exact GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | (intros; apply GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula <;> assumption)
end
