module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle002
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainHighest

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)

theorem kRel_map {n : ℕ} {A B : Type} [Ring A] [Ring B] (ε : Fin n → Bool) (f : A →+* B)
    (F : Fin n → Fin n → A) (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul] at this
  rw [this]
  congr 1 <;> split_ifs <;> simp

theorem fdual_single {n : ℕ} {ε : Fin n → Bool} {U : Type} [AddCommGroup U] [Module ℂ U]
    (EU : Fin n → Fin n → Module.End ℂ U) (g : Fin n → Fin n → Finset (NC ε) → Finset (NC ε) → ℝ)
    (hg : ∀ (c d : Fin n) (x : Ch ε U) (A : Finset (NC ε)), Gop ε c d x A = ∑ B, (g c d A B : ℂ) • x B)
    (a b : Fin n) (A B : Finset (NC ε)) (u : U) :
    Fdual ε EU a b (Pi.single A u) B =
      (Pi.single A (EU a b u) : Ch ε U) B - (g b a B A : ℂ) • u := by
  unfold Fdual
  rw [LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg]
  congr 1
  · by_cases h : B = A
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single A]
    · simp
    · intro C _ hC; simp [hC]
    · simp

theorem aux₃ : FRel → GFacts → GamDom → KHWExists → HWMap → PRV := by
  intro hF hG hγ hK hM n ε lam V _ _ E v S hlam hE hEu hv hS hSt hvS
  obtain ⟨γ, hγ1, hγ2⟩ := hγ n ε lam hlam
  obtain ⟨U, _, _, _, EU, u, hU, hUu, hu0, hu⟩ := hK n ε γ hγ2
  obtain ⟨g, hg, hgs, hgc, hgd, hgl⟩ := hG n ε
  let T : Type := PiLp 2 (fun _ : Finset (NC ε) => U)
  let e : Ch ε U ≃ₗ[ℂ] T := (WithLp.linearEquiv 2 ℂ (Finset (NC ε) → U)).symm
  have he : ∀ (x : Ch ε U) A, (e x).ofLp A = x A := fun _ _ => rfl
  let ET : Fin n → Fin n → Module.End ℂ T := fun a b => e.conjRingEquiv.toRingHom (Fdual ε EU a b)
  have hET : ∀ a b x, ET a b (e x) = e (Fdual ε EU a b x) := by
    intro a b x
    rfl
  have hTrel : KRel ε ET := kRel_map ε _ _ (hF n ε U EU hU).2
  have hTu : KUnit ε ET := by
    intro a b hab x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hET, hET, PiLp.inner_apply, PiLp.inner_apply]
    simp only [he, Fdual, LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg, inner_sub_left,
      inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    congr 1
    · exact Finset.sum_congr rfl fun A _ => hUu a b hab _ _
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      rw [hgs b a B A]
  have ht0 : e (Pi.single (A1 ε) u) ≠ 0 := by
    intro h
    have := he (Pi.single (A1 ε) u) (A1 ε)
    rw [h] at this
    apply hu0
    simpa using this.symm
  have ht : KHighest ε ET (lowK ε lam) (e (Pi.single (A1 ε) u)) := by
    constructor
    · intro a
      rw [hET, ← map_smul]
      congr 1
      funext B
      rw [fdual_single EU g (hg U), hu.1 a, hgd]
      by_cases h : B = A1 ε
      · subst h
        have h1 := hγ1 a
        simp only [gam, Pi.add_apply] at h1
        simp only [Pi.single_eq_same, if_true, Pi.smul_apply, ← sub_smul, ← h1]
        congr 1
        push_cast
        ring
      · simp [h]
    · intro a b hab hε
      rw [hET, map_eq_zero_iff _ e.injective]
      funext B
      rw [fdual_single EU g (hg U), hu.2 a b hab hε, hgl b a B hab]
      simp
  obtain ⟨φ, hφ1, hφ2⟩ := hM n ε T V ET E (lowK ε lam) _ v S hTrel hTu hE hEu ht0 ht hv hS hSt hvS
  let c : Ch ε V := fun A => if A.card = (A1 ε).card then φ (e (Pi.single A u)) else 0
  have key : ∀ a b, ε a = ε b → ∀ A, Fop ε E a b c A =
      if A.card = (A1 ε).card then φ (e (Pi.single A (EU a b u))) else 0 := by
    intro a b hab A
    unfold Fop
    rw [LinearMap.add_apply, Pi.add_apply, lift_apply, hg]
    by_cases hA : A.card = (A1 ε).card
    · have h1 : Fdual ε EU a b (Pi.single A u) =
          Pi.single A (EU a b u) - ∑ B, (g a b A B : ℂ) • (Pi.single B u : Ch ε U) := by
        funext B
        rw [fdual_single EU g (hg U), Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single B, hgs b a B A]
        · simp
        · intro C _ hC; simp [hC.symm]
        · simp
      have h2 : ∀ B, (g a b A B : ℂ) • c B = (g a b A B : ℂ) • φ (e (Pi.single B u)) := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_true]
      simp only [h2]
      simp only [c, hA, if_true]
      rw [← hφ2 a b hab, hET, h1]

      simp only [map_sub, map_sum, map_smul]
      abel
    · have h2 : ∀ B, (g a b A B : ℂ) • c B = 0 := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_false, smul_zero]
      simp only [h2]
      simp [c, hA]
  refine ⟨c, fun A hA => by simp [c, hA], ⟨fun a => ?_, fun a b hab hε => ?_⟩, by simp [c, hφ1]⟩
  · funext A
    rw [key a a rfl, hu.1 a, Pi.smul_apply, hγ1 a]
    by_cases hA : A.card = (A1 ε).card
    · simp only [c, hA, if_true]
      rw [Pi.single_smul, map_smul, map_smul]
    · simp [c, hA]
  · funext A
    rw [key a b hε, hu.2 a b hab hε]
    simp

end GlobalTheory.CompanionTheory.ChainHighest
end
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DSChainAdj

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

theorem sg_insert (i : NC ε) (A : Finset (NC ε)) : sg i (insert i A) = sg i A := by
  unfold sg
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

theorem conj_sg (i : NC ε) (A : Finset (NC ε)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

theorem sum_insert_erase (i : NC ε) (f : Finset (NC ε) → Finset (NC ε) → ℂ) :
    (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ B : Finset (NC ε), if i ∈ B then f B (B.erase i) else 0 := by
  have h1 : (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ A ∈ univ.filter (fun A : Finset (NC ε) => i ∉ A), f (insert i A) A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : i ∈ A <;> simp [h]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun A => insert i A) (fun B => B.erase i) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    exact Finset.erase_insert hA'
  · intro B hB
    have hB' : i ∈ B := by simpa using hB
    exact Finset.insert_erase hB'
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    simp only [Finset.erase_insert hA']

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem term_adj (i : NC ε) (T T' : Module.End ℂ V) (h : ∀ x y : V, ⟪T x, y⟫_ℂ = -⟪x, T' y⟫_ℂ) (w x : Ch ε V) :
    ip (lift ε T (ann i w)) x = -ip w (lift ε T' (cre i x)) := by
  unfold ip
  have key := sum_insert_erase i (fun B A => sg i B * ⟪T (w B), x A⟫_ℂ)
  have hL : (∑ A, ⟪lift ε T (ann i w) A, x A⟫_ℂ) =
      ∑ A : Finset (NC ε), if i ∈ A then 0 else sg i (insert i A) * ⟪T (w (insert i A)), x A⟫_ℂ := by
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [ann, hA]
    · simp [ann, hA, conj_sg, sg_insert, mul_comm]
  have hR : -(∑ A, ⟪w A, lift ε T' (cre i x) A⟫_ℂ) =
      ∑ B : Finset (NC ε), if i ∈ B then sg i B * ⟪T (w B), x (B.erase i)⟫_ℂ else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [cre, hA, h]
    · simp [cre, hA]
  rw [hL, hR, key]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (x : Ch ε V) :
    ip (∑ i ∈ s, f i) x = ∑ i ∈ s, ip (f i) x := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, sum_inner]

theorem ip_sum_right {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (w : Ch ε V) :
    ip w (∑ i ∈ s, f i) = ∑ i ∈ s, ip w (f i) := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, inner_sum]

theorem adj : CompanionTheory.D.DSIC.Adj := by
  intro n ε V _ _ E hE w x
  unfold bd bdA cob
  rw [LinearMap.sum_apply, LinearMap.sum_apply, ip_sum_left, ip_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  refine term_adj i _ _ (fun a b => ?_) w x
  have h := hE i.1.1 i.1.2 a b
  have h1 := i.2.1
  have h2 := i.2.2
  rw [h]
  simp [Formalism.REAL.sgn, h1, h2]

end GlobalTheory.CompanionTheory.DSChainAdj
end

section

open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.DSSmLin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mul_mem_UJset {n : ℕ} (ε : Fin n → Bool) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

theorem ex_mem_UJset {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    ex X t ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem inG_add {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem inG_smul {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    inG ε ((s : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
    ← smul_add, hX, smul_zero]

theorem smLin : CompanionTheory.D.DSIC.SmLin := by
  intro n ε H _ _ σ hσ
  obtain ⟨⟨h1, hm⟩, -, -⟩ := hσ
  have h : RepOn (UJset ε) σ := ⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩
  refine ⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_,
    fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩
  · exact IsSm.add (G := UJset ε) hv hw
  · exact IsSm.smul (G := UJset ε) hv c
  · exact IsSm.apply h hv hg
  · have hv' : IsSm (UJset ε) σ v := hv
    refine ⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩
    rw [List.mem_singleton.1 hY]
    exact ex_mem_UJset hX t
  · have hv' : IsSm (UJset ε) σ v := hv
    obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv' 1 h.one_mem
    have key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z := fun Z hZ => by
      have hd : HasDerivAt (fun t => ex Z t) Z 0 := by simpa using hasDerivAt_mul_ex 1 Z
      exact (hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv
    refine ⟨?_, fun s => ?_⟩
    · rw [key _ (inG_add hX hY), key _ hX, key _ hY, map_add (f := _)]
    · rw [key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]

end GlobalTheory.CompanionTheory.DSSmLin
end

section

open CompanionTheory.Rg.Fl Matrix
namespace GlobalTheory.CompanionTheory.CartGL

theorem stCartanGL : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_uniformizer_nonarchimedean L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.congruence_subgroups_neighborhood_basis L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0, GlobalTheory.T.congruence_subgroup_is_compact L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := GlobalTheory.T.compact_subgroup_finite_open_cosets (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (GlobalTheory.T.congruence_subgroup_is_compact L n 1 zero_le_one le_rfl) (GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.cartan_decomposition_gl_nonarchimedean L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, GlobalTheory.T.antitone_powers_in_dominant_monoid L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := GlobalTheory.T.near_identity_upper_lower_factorization L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_upper_congruence L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_lower_congruence L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group

end GlobalTheory.CompanionTheory.CartGL
end
