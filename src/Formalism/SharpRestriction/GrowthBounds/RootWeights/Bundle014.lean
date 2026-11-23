module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_kills_operator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (a b : Fin n) (x : V) : Inv (E a b x) = 0 := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.ker (Inv * E a b) := by
    intro mu y hy
    rw [LinearMap.mem_ker, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hy0, hyr⟩ := hinv y hy
      have : E a b y = 0 := by
        rcases lt_trichotomy a b with h | h | h
        · exact hyr a b h
        · subst h
          have := (mem_weightSpace_iff_diagonal_eigen E 0 y).1 hy0 a
          simpa using this
        · exact weight_zero_lowering_kills_raising hE hy0 b a (ne_of_lt h) (hyr b a h)
      rw [this, map_zero]
    · exact hInv.2 mu hmu _ (isotypic_stable_under_gl_operator E mu a b y hy)
  have : (⊤ : Submodule K V) ≤ LinearMap.ker (Inv * E a b) := by
    rw [← htop]
    exact iSup_le hle
  have h3 := this (Submodule.mem_top (x := x))
  rwa [LinearMap.mem_ker, Module.End.mul_apply] at h3

theorem invariant_projection_kills_nonzero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (μ : Fin n → ℤ) (hμ : μ ≠ 0) (x : V)
    (hx : x ∈ weightSp E μ) : Inv x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (funext h)
  have h1 := (mem_weightSpace_iff_diagonal_eigen E μ x).1 hx a
  have h2' : (μ a : K) ≠ 0 := by exact_mod_cast ha
  have h3 : x = E a a (((μ a : K))⁻¹ • x) := by
    rw [map_smul, h1, smul_smul, inv_mul_cancel₀ h2', one_smul]
  rw [h3]
  exact invariant_projection_kills_operator D h2 E hE Inv hInv a a _

theorem invariant_projection_through_zero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (x : V) : Inv x = Inv (Θ 0 x) := by
  classical
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  set box : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hbox
  have hb : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hb x
  have h0 : (0 : Fin n → ℤ) ∈ box := by
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    constructor <;> simp
  conv_lhs => rw [← hsum]

  rw [map_sum, Finset.sum_eq_single_of_mem 0 h0]
  intro μ _ hμ
  exact invariant_projection_kills_nonzero_weight D h2 E hE Inv hInv μ hμ _ (weight_projection_mem_weightSpace E hE Θ hΘ μ x)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_extremal_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (π : Module.End K V) (hπ : IsWtProj E 0 π)
    (ord : List (Fin n × Fin n)) (hord : NormalOrder n ord) (T : ℕ) (hT : Module.finrank K V ≤ T) :
    Inv = pp E 0 ord T * π := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hkill := nontrivial_isotypic_weight_zero_killed hE hs
  obtain ⟨_, h5b, h5c⟩ := h5 K V n E hE 0 (by
    intro a b hab
    have : (a : ℕ) < (b : ℕ) := hab
    simp only [Pi.zero_apply]
    omega) ord hord T hT
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    intro mu x hx
    rw [LinearMap.mem_eqLocus, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hx0, hxr⟩ := hinv x hx
      rw [hInv.1 x hx, hπ.1 x hx0, h5c x hx0 hxr]
    · rw [hInv.2 mu hmu x hx, hkill _ π hπ h5b mu hmu x hx]
  have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    rw [← htop]
    exact iSup_le hle
  exact LinearMap.ext fun x => this (Submodule.mem_top (x := x))

theorem root_multiple_apply_first {n : ℕ} (a b : Fin n) (hab : a ≠ b) (k : ℕ) : ((k : ℤ) • rootW a b) a = k := by
  simp [rootW, Pi.single_apply, hab]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem sDegs_eq_support_mul_Phi_twistSub {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (j : Fin n) (H : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j H = (mul_Phi _ _ (twistSub LL S j H)).coeff.support := by
  ext k
  simp only [sDegs, Finset.mem_biUnion, Finsupp.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · rintro ⟨m, -, hk⟩ h0
    apply hk
    rw [← mul_Phi_coeff, h0, MvPolynomial.coeff_zero]
    rfl
  · intro hk
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [mul_Phi_coeff] at hm
    refine ⟨m, fun h => hm ?_, hm⟩
    rw [h]
    rfl

theorem mul_valS_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
  rw [valS, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_lam1S_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
  rw [lam1S, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  rw [mul_valS_eq LL S F, mul_valS_eq LL S G, mul_valS_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans ?_ (Finset.inf_mono Finsupp.support_add)
  rw [Finset.inf_union]
  exact le_rfl

theorem mul_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  rw [mul_lam1S_eq LL S F, mul_lam1S_eq LL S G, mul_lam1S_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans (Finset.sup_mono Finsupp.support_add) ?_
  rw [Finset.sup_union]
  exact le_rfl

theorem valuation_bound_det_power_factor (R : Type) [Field R] (ι : Type) (LL : Letters ι) (r : ℕ) [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true)
    (G H : MvPolynomial (ι × Fin r) R) (m : ℕ) (hG : G = (detA (R := R) A) ^ m * H) (S' : Set ι) :
    valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ) := by
  have hd := mul_valS_detA_le (R := R) LL A hA hv S'
  have hpow : ∀ k : ℕ, valS LL S' ((detA (R := R) A) ^ (k + 1)) ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [pow_succ, mul_valS_mul]
      calc valS LL S' ((detA (R := R) A) ^ (k + 1)) + valS LL S' (detA (R := R) A)
          ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := add_le_add ih hd
        _ = (((k + 1 + 1 : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
  subst hG
  rcases m with _ | k
  · simp
  · rw [mul_valS_mul, add_comm (valS LL S' _) (valS LL S' H)]
    exact add_le_add (le_refl _) (hpow k)

def GlOperatorsFormRepresentation : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (h : GlOperatorsFormRepresentation) : ConclusionE D := by
  intro R _ ι _ LL r _ S A hA hAS
  exact ⟨h R ι LL r S A hA hAS,
    fun G H m hG S' => valuation_bound_det_power_factor R ι LL r A hA (fun l => (hAS l).2) G H m hG S'⟩

def GeneratedModuleWeightDescription : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι),
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ), ((th : WithTop ℤ) ≤ valS LL S G ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), th ≤ mu (lastIdx n))) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ), (lam1S LL S G ≤ (M : WithBot ℤ) ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), mu 0 ≤ M))

theorem valuations_additive_of_generated_weight_description (D : Formalism.BasicNotions.D7) (h : GeneratedModuleWeightDescription) : ValuationsAdditive D := by
  intro R _ ι _ LL n _ S
  exact ⟨mul_valS_mul LL S, mul_valS_add LL S, mul_lam1S_mul LL S, mul_lam1S_add LL S,
    (h R ι LL n S).1, (h R ι LL n S).2⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem operator_list_lattice_scaling {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p : ℕ)
    (L : Submodule O (MvPolynomial σ (KK O))) (W : Submodule (KK O) (MvPolynomial σ (KK O)))
    (l : List (Module.End (KK O) (MvPolynomial σ (KK O)) × ℕ))
    (hW : ∀ eD ∈ l, ∀ F ∈ W, eD.1 F ∈ W)
    (hL : ∀ eD ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ eD.2) • eD.1 F ∈ L) :
    ∀ F ∈ W, F ∈ L → (l.map Prod.fst).prod F ∈ W ∧
      ((p : KK O) ^ (l.map Prod.snd).sum) • (l.map Prod.fst).prod F ∈ L := by
  induction l with
  | nil =>
    intro F hF hFL
    simp [hF, hFL]
  | cons eD l ih =>
    intro F hF hFL
    have hW' : ∀ e ∈ l, ∀ F ∈ W, e.1 F ∈ W := fun e he => hW e (List.mem_cons_of_mem _ he)
    have hL' : ∀ e ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ e.2) • e.1 F ∈ L :=
      fun e he => hL e (List.mem_cons_of_mem _ he)
    obtain ⟨h1, h2⟩ := ih hW' hL' F hF hFL
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨hW eD (by simp) _ h1, ?_⟩
    have h3 := hL eD (by simp) _ (W.smul_mem ((p : KK O) ^ (l.map Prod.snd).sum) h1) h2
    rw [map_smul, smul_smul, ← pow_add] at h3
    exact h3

theorem polynomial_isotypic_lattice_of_parts (D : Formalism.BasicNotions.D7) (hCR : CompleteReducibilityIsotypic) (hOrth : ContravariantIsotypicOrthogonal) (hDom : HighestWeightDominant)
    (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (hLat : AdmissibleDVRIntegralFormLatticesStable) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D := by
  intro p n' O _ _ _ S0 hG n ι _ LL N Ss hmono
  obtain ⟨hchar, hLat'⟩ := hLat p n' O S0 hG
  obtain ⟨hL1, hL2, BBs, hBB, hL3⟩ := hLat' n ι LL
  refine ⟨fun i => hL1 (Ss i), ?_⟩
  intro ee hee
  obtain ⟨hP1, hP2, hP3, -, -, -, B, hB1, hB2⟩ := hPol (KK O) ι n LL
  have hT : ∀ S : Set ι, (⨆ mu : Fin n → ℤ, isoSub (glOps (KK O) n LL S) mu) = ⊤ :=
    fun S => hCR (KK O) _ n _ (hP1 S)

  have hdis : ∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
      ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam := by
    intro i lam S' hS' a b
    refine isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => ?_
    exact isotypic_stable_commuting _ _ (fun c d => (hP2 (Ss i) S' hS' c d a b).symm) mu x hx
  have hle : ∀ i j, i ≤ j → ∀ lam a b,
      ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam := by
    intro i j hij lam a b
    rw [hP3 (Ss i) (Ss j) (hmono hij) a b, mul_add, add_mul, hdis i lam _ Set.disjoint_sdiff_right a b]
    congr 1
    exact isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => isotypic_stable_gl_operator _ mu a b x hx
  have hcomm' : ∀ i j, i ≤ j → ∀ lam mu, ee i lam * ee j mu = ee j mu * ee i lam := by
    intro i j hij lam mu
    refine (isotypic_projector_commutes _ (hT (Ss j)) mu _ (hee j mu) _ fun nu x hx => ?_).symm
    exact isotypic_stable_commuting _ _ (fun c d => hle i j hij lam c d) nu x hx
  refine ⟨hle, hdis, ?_, ?_, ?_⟩
  · intro i j lam mu
    rcases le_total i j with h | h
    · exact hcomm' i j h lam mu
    · exact (hcomm' j i h mu lam).symm
  · intro i lam F G
    rw [← hB1, ← hB1]
    exact isotypic_projector_selfAdjoint _ (hT (Ss i)) lam _ (hee i lam) B
      (hOrth (KK O) _ n _ (hP1 (Ss i)) B (fun a b x y => hB2 (Ss i) a b x y)) F G
  · intro T d F hF
    have hstep := fun (i : Fin N) (lam : Fin n → ℤ) =>
      isotypic_projector_lattice_scaling D hDom hRes hPol h13 p n' O S0 hG n ι LL (Ss i) d lam (ee i lam) (hee i lam)
    have main : ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
        (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
        MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ → F ∈ L →
        ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
          (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ L := by
      intro L hst hFG hMQ hFL
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      have h := operator_list_lattice_scaling p L (Pol (KK O) n d)
        (List.ofFn fun i => (ee i (t i), N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1)))
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).1)
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).2 L (hst (Ss i)) hFG hMQ) F hF hFL
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h.2
    obtain ⟨h1, h2, h3, h4⟩ := hL3 d
    refine ⟨fun hFL => main _ (fun S u hu => (hL2 S u hu).1) h1 h2 hFL, fun hFB => ?_⟩
    rw [← hBB] at hFB ⊢
    exact main BBs (fun S u hu F hF => (hBB _).2 ((hL2 S u hu).2 F ((hBB _).1 hF))) h3 h4 hFB

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def LatticeNablaDeltaBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      (∀ x ∈ Nabla (O := O) E lam v, ((p : O) ^ (N0 n * deF p n (ellWt lam))) • x ∈ Delta (O := O) E v)

theorem highest_weight_lattice_of_first_part (D : Formalism.BasicNotions.D7) (h : LatticeNablaDeltaBound) : NablaDeltaComparisonField D := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI
  refine ⟨h p n' O S hR n lam V E v hI, ?_⟩
  intro M hM _ hl
  have := dvr_fraction_field_char_zero_prime S hR.prime
  exact highest_weight_lattice_bounds E hI.1.2.2 lam v M hM.1 hl

end Formalism.MainNotions.G.GLWeightTheory
end
end
