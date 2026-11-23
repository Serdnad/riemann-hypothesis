module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Formalism.SharpRestriction.GrowthBounds.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
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
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.PairingDivisors.StatementH

@[expose] public section

section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevClosed

open Polynomial

theorem mem_adjoin_inv_of_isIntegral {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨f, hm, hf⟩ := hi
  letI : Invertible z := invertibleOfNonzero hz
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) z f
  rw [hf, invOf_eq_inv] at h1
  have h2 : eval₂ (algebraMap R K) z⁻¹ f.reverse = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hz)
  have h3 := divX_mul_X_add f.reverse
  rw [coeff_zero_reverse, hm.leadingCoeff] at h3
  have h4 := congrArg (eval₂ (algebraMap R K) z⁻¹) h3
  rw [h2, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, map_one] at h4
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have h5 : z = -(aeval z⁻¹ (divX f.reverse)) := by
    rw [aeval_def]
    linear_combination z * h4 - eval₂ (algebraMap R K) z⁻¹ (divX f.reverse) * hzz
  have hm' : -(aeval z⁻¹ (divX f.reverse)) ∈ Algebra.adjoin R {z⁻¹} :=
    neg_mem (aeval_mem_adjoin_singleton R _)
  rwa [← h5] at hm'

theorem lev_closed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
      IsInt (p := p) (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h; apply hb0; rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := mem_adjoin_inv_of_isIntegral hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem

end GlobalTheory.K5.LevClosed
end
end

section

open Formalism.MainNotions.G MvPolynomial

noncomputable section

namespace GlobalTheory.PrescribedRank

variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def noPlaces : Places p O Kf where
  w := 0
  nV := 0
  n' := fun _ => 0
  W := fun _ => O
  Qq := fun _ => Kf
  ι := fun _ => RingHom.id Kf
  σ := fun _ => RingEquiv.refl Kf
  j := fun _ => RingHom.id O
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun _ _ _ => 0
  dom := fun v => v.elim0

instance : IsEmpty (Fin (noPlaces p O Kf).nV) := inferInstanceAs (IsEmpty (Fin 0))

def trivLevel : Level (noPlaces p O Kf) where
  Γ := PUnit
  act := fun _ => 1
  χ := 1

theorem tup_eq (L L' : (noPlaces p O Kf).Tup) : L = L' := funext fun v => isEmptyElim v

theorem isLatTup (L : (noPlaces p O Kf).Tup) : (noPlaces p O Kf).IsLatTup L := fun v => isEmptyElim v

theorem actX_apply (γ : (trivLevel p O Kf).Γ) (x : (noPlaces p O Kf).Xsp) :
    (trivLevel p O Kf).actX γ x = x := by
  have h : ∀ G, (noPlaces p O Kf).subst G = AlgHom.id Kf _ := fun G =>
    MvPolynomial.algHom_ext fun i => isEmptyElim i.1
  unfold Level.actX Places.natAct
  rw [h, Fintype.prod_empty]
  simp

theorem htupW_eq (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    rw [Fintype.prod_empty]
    rfl
  · rintro rfl
    exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩

theorem mem_funMod (Hv : (noPlaces p O Kf).Tup → Submodule O (noPlaces p O Kf).Xsp)
    (F : (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) :
    F ∈ (trivLevel p O Kf).funMod Hv ↔ ∀ L, F L ∈ Hv L := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩ L
    exact h L (isLatTup p O Kf L)
  · intro h
    refine ⟨⟨fun L _ => h L, fun L hL => absurd (isLatTup p O Kf L) hL⟩, fun γ L => ?_⟩
    have hχ : (trivLevel p O Kf).χ γ = 1 := rfl
    rw [tup_eq p O Kf ((trivLevel p O Kf).smul γ L) L, hχ]
    simp [actX_apply]

theorem finClasses : (trivLevel p O Kf).FinClasses :=
  ⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ =>
    ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩

def gat (d : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := noPlaces p O Kf
  comp := Fin d
  lev := fun _ => trivLevel p O Kf
  e := 0

def constMap (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) where
  toFun c := fun i _ => c i • (1 : (noPlaces p O Kf).Xsp)
  map_add' a b := by
    funext i L
    simp [add_smul]
  map_smul' a b := by
    funext i L
    simp [mul_smul]

theorem constMap_injective (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h : c i • (1 : (noPlaces p O Kf).Xsp) = 0 := congrFun (congrFun hc i) (fun v => isEmptyElim v)
  have h2 := congrArg (AddMonoidAlgebra.coeff · 0) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero,
    Algebra.smul_def, mul_one] at h2
  apply hinj
  rw [h2]
  simp

theorem range_constMap (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by
  ext F
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ i L
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    refine ⟨fun i => c i (fun v => isEmptyElim v), ?_⟩
    funext i L
    rw [tup_eq p O Kf L (fun v => isEmptyElim v)]
    exact hc i _

theorem gat_d (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) : (gat p O Kf d).d = d := by
  have h : (gat p O Kf d).d = Module.finrank O
      (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW) := rfl
  rw [h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]
  simp

theorem GAtP₂ : ∀ (p d : ℕ), p.Prime → ∃ G : GAtP p, G.d = d ∧ G.FinClasses := by
  intro p d hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨gat p ℤ_[p] ℚ_[p] d, gat_d p _ _ d (IsFractionRing.injective ℤ_[p] ℚ_[p]),
    fun _ => finClasses p _ _⟩

end GlobalTheory.PrescribedRank
end
end

section

noncomputable section

namespace GlobalTheory.PointIrredCompare

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
      have : (g⁻¹ : G F Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ * g) x = x
      simp
    rwa [e] at h

theorem Ine_le_of_normal [IsAlgClosure F Ω] {A B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) (Hs : Subgroup (G F Ω)) [hn : Hs.Normal]
    (h : Ine (F := F) A ≤ Hs) : Ine (F := F) B ≤ Hs := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hB
  intro σ hσ
  have := hn.conj_mem _ (h (conj_mem_Ine_of_smul hσ)) g
  simpa [mul_assoc] using this

end Galois

section Hyps

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) : A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h : ∀ l : List ℝ, A.lpDim (l.foldr
      (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) =
      p.a * l.length := by
    intro l
    induction l with
    | nil => simp [A.lpDim_zero]
    | cons a l ih => simp only [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons]; ring
  unfold spehLoc
  rw [h]
  simp

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => simp [isoLoc, rankIso, A.lpDim_zero]
  | cons p P ih =>
    have : isoLoc N A (p :: P) w = A.lpSum (spehLoc N A p w) (isoLoc N A P w) := rfl
    rw [this, A.lpDim_sum, ih, lpDim_spehLoc]
    simp [rankIso]

theorem rank_of_hasParamX {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r := by
  obtain ⟨P, -, h1, -, h3, -⟩ := h
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · simp only [rankIso, twistIso, muPart, List.map_map, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Ranks.nV] at h3 ⊢
    have e : List.map ((fun p : Part A.CG => p.a * p.d) ∘
        fun p : Part A.CG => (⟨p.a, A.tw p.π A.etaTinv, p.d⟩ : Part A.CG)) Sig =
        List.map (fun p : Part A.CG => p.a * p.d) Sig := rfl
    rw [e] at h3
    omega

def FullLabels (Sig : List (Part A.CG)) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = A.lpDim (isoLoc N A Sig (A.plGw k v))

theorem fullLabels_of_good {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig)
    (hg : goodSig N A Sig) : FullLabels N A Sig := fun k v => by
  rw [lpDim_isoLoc, (rank_of_hasParamX N A h).2]
  exact ((hg k).1.1 v).2.1


end Hyps

end GlobalTheory.PointIrredCompare

end
end

section

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

theorem sum_comp_le_sum_of_injOn {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∑ t ∈ T, g (f t) ≤ ∑ s ∈ S, g s := by
  rw [← Finset.sum_image (g := f) (f := g) hf]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hg s hs)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
  exact hS t ht

theorem sum_le_sum_add_card_mul {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (u : ι → ℝ) (c : ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hu : ∀ t ∈ T, u t ≤ g (f t) + c) :
    ∑ t ∈ T, u t ≤ ∑ s ∈ S, g s + (T.card : ℝ) * c := by
  have h1 := Finset.sum_le_sum hu
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 := sum_comp_le_sum_of_injOn T S f g hf hS hg
  linarith

theorem count_factors : ∀ (e p q e0 h0 : ℕ), e0 + p = e + q → e0 ≤ h0 → ∀ (v a n0 : ℤ → ℝ) (er : ℝ), 0 ≤ er → (∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q → 0 ≤ a s ∧ 0 ≤ n0 s ∧ v s ≤ a s + er ∧ -(v s) ≤ a s + n0 s) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → v s = v (1 - s)) → (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s) + (∑ k ∈ range p, v ((e : ℤ) + q - k)) - (∑ k ∈ range q, v ((e : ℤ) + k + 1)) ≤ 4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) + ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
  intro e p q e0 h0 he hle v a n0 er her H hsym
  set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS
  have hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q := by
    intro s; simp [hS]
  have ha : ∀ s ∈ S, 0 ≤ a s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1
  have hn : ∀ s ∈ S, 0 ≤ n0 s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1
  have hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s
      = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s := by
    rw [← Finset.sum_union]
    · congr 1
      ext s
      simp only [mem_union, mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [mem_Icc] at h1 h2
      omega
  have b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er
      (fun x _ y _ h => by simpa using h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        rw [hsym t ht.1 ht.2]
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 - (e0 : ℤ)) 0).card = e0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er
      (fun x _ y _ h => h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er := by
    have := sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a
      (fun k : ℕ => v ((e : ℤ) + q - k)) er
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha
      (fun t ht => by
        simp only [mem_range] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    rwa [card_range] at this
  have b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0 := by
    have := sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1)
      (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega)
      (fun s hs => add_nonneg (ha s hs) (hn s hs))
      (fun t ht => by
        simp only [mem_range] at ht
        rw [add_zero]
        exact (H _ (by omega) (by omega)).2.2.2)
    rwa [card_range] at this
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at b4
  have hN : 0 ≤ ∑ s ∈ S, n0 s := Finset.sum_nonneg hn
  have hA : 0 ≤ ∑ s ∈ S, a s := Finset.sum_nonneg ha
  have hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
    refine mul_le_mul_of_nonneg_right ?_ her
    have : e0 + h0 + p ≤ 2 * (h0 + p + q) := by omega
    exact_mod_cast this
  rw [hsplit]
  linarith

end GlobalTheory.Square
end
