module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKSwapCup

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I q ∈ L.T :=
  (Submodule.Quotient.mk_surjective I q).choose.2

theorem mk_liftQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L I q, liftQ_mem L I q⟩ : ↥L.T) : ↥L.T ⧸ I) = q :=
  (Submodule.Quotient.mk_surjective I q).choose_spec

theorem liftQ_sub (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (x : ↥L.T)
    (q : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (hq : Submodule.Quotient.mk x = q) :
    ∃ t ∈ L.T, Formalism.MainNotions.LocalSituation.liftQ L _ q - (x : V) = (algebraMap O LL ϖ) ^ r • t := by
  have h : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x ∈
      (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) :=
    (Submodule.Quotient.eq _).1 ((mk_liftQ L _ q).trans hq.symm)
  generalize hy : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x = y at h
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨t, -, ht⟩ := h
  subst ht
  refine ⟨t, t.2, ?_⟩
  rw [← map_pow, algebraMap_smul, ← Submodule.coe_smul, ← hy]
  rfl

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by subst hr; simp⟩
    · exact ⟨0, by rw [h, zero_pow hr.ne', mul_zero, map_zero]⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h, one_pow, map_one]⟩

end Gen
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cong
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def swapF (L : Lattice (O := O) ρ) (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O) (r : ℕ)
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (d : G → V') (g : G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)

theorem swap_cong (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hint : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ e : O, P x y = algebraMap O LL e)
    (χ : G → LL) (hχ : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (hs : ∀ g h, s (g * h) = s g + actQ L _ hI g (s h))
    (d : G → V') (hdT : ∀ g, d g ∈ L'.T) (hdmul : ∀ g h, d (g * h) = d g + ρ' g (d h))
    (q : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T))
    (hq : ∀ h, Submodule.Quotient.mk (⟨d h, hdT h⟩ : ↥L'.T) = q h) (g h : G) :
    ∃ e : O, GlobalTheory.BKFinLevel.cupQ L L' P ϖ r s q (g, h)
      + cupLD L P.flip d (fun g => GlobalTheory.BKFinLevel.ioL L ϖ r (s g)) (g, h)
      + (χ g * swapF L P ϖ r s d h - swapF L P ϖ r s d (g * h) + swapF L P ϖ r s d g)
      = algebraMap O LL e := by
  have huT : ∀ g, Formalism.MainNotions.LocalSituation.liftQ L _ (s g) ∈ L.T := fun g => liftQ_mem L _ (s g)
  have hmk : ∀ g, (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s g :=
    fun g => mk_liftQ L _ (s g)

  have hq3 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ +
      actT L g ⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s h), huT h⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s (g * h) := by
    rw [hs g h]
    exact (Submodule.Quotient.mk_add _).trans
      (congrArg₂ (· + ·) (hmk g) (congrArg (actQ L _ hI g) (hmk h)))
  obtain ⟨t3, ht3, hu3⟩ := liftQ_sub L ϖ r _ _ hq3

  obtain ⟨t1, ht1, hd1⟩ := liftQ_sub L' ϖ r _ _ (hq h)

  have hio : GlobalTheory.BKFinLevel.ioL L ϖ r (s h) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) :=
    (congrArg (GlobalTheory.BKFinLevel.ioL L ϖ r) (mk_liftQ L _ (s h))).symm.trans
      (GlobalTheory.BKFinLevel.ioL_mk L ϖ r _)
  have hl : (Submodule.Quotient.mk (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))) : V ⧸ L.T) =
      GlobalTheory.BKFinLevel.ioL L ϖ r (s h) :=
    (Submodule.Quotient.mk_surjective L.T _).choose_spec
  have ht2 := (Submodule.Quotient.eq _).1 (hl.trans hio)
  show ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (ρ' g (Formalism.MainNotions.LocalSituation.liftQ L' _ (q h)))
      + P.flip (d g) (ρ g (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))))
      + (χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h))
        - (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h))) (d (g * h))
        + (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)) = algebraMap O LL e
  generalize liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h)) = w at ht2 ⊢
  obtain ⟨t2, ht2', rfl⟩ : ∃ t2 ∈ L.T,
      w = (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h) + t2 :=
    ⟨_, ht2, by abel⟩
  have E1 : Formalism.MainNotions.LocalSituation.liftQ L' _ (q h) = d h + (algebraMap O LL ϖ) ^ r • t1 :=
    sub_eq_iff_eq_add'.1 hd1
  have E3 : Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h)) = Formalism.MainNotions.LocalSituation.liftQ L _ (s g) +
      ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) + (algebraMap O LL ϖ) ^ r • t3 :=
    sub_eq_iff_eq_add'.1 hu3
  obtain ⟨e0, he0⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r
  obtain ⟨e1, he1⟩ := hint _ (huT g) _ (L'.stable g _ ht1)
  obtain ⟨e2, he2⟩ := hint _ (L.stable g _ ht2') _ (hdT g)
  obtain ⟨e3, he3⟩ := hint t3 ht3 (d g + ρ' g (d h)) (by rw [← hdmul]; exact hdT _)
  refine ⟨e0 * e1 + e2 - e0 * e3, ?_⟩
  have E5 : χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h)) =
      (algebraMap O LL ϖ)⁻¹ ^ r * P (ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h))) (ρ' g (d h)) := by
    rw [hχ]; ring
  rw [E1, E3, hdmul, E5]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.flip_apply] at he3 ⊢
  rw [map_sub, map_add (f := _), map_mul, map_mul, ← he0, ← he1, ← he2, ← he3]
  ring

end Cong
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem cobO_swap (hopen : IsOpen (Set.range (algebraMap O LL)))
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) {A A' : GRep G Qp LL O}
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hm : IsDualLat1 PD LA LA' m) (ϖ : O) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (s : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hs : s ∈ quotientCocycles LA _ hI)
    (d : ↥(latticeCocycles LA')) :
    CobO PD L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔
      CobO PD L1 (cupLD LA m.flip (d : G → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  have hdT : ∀ g, (d : G → A'.V) g ∈ LA'.T := fun g => d.2.2 g (Set.mem_univ g)
  have hint : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ e : O, m x y = algebraMap O LL e :=
    fun x hx y hy => (hm.2 y).1 hy x hx
  have key := swap_cong LA LA' m hint (fun g => ((cycLL PD LL g : LLˣ) : LL)) hm.1.1 ϖ r hI s
    hs.2 (d : G → A'.V) hdT d.2.1.2 (redT LA' _ d) (fun _ => rfl)
  let Fq : G → LL ⧸ L1.T := fun g =>
    Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)
  have hFq : Fq ∈ ReciprocityTheory.Def.C1 G (⊤ : Submodule O (LL ⧸ L1.T)) := by
    refine ⟨?_, fun _ => Submodule.mem_top⟩
    have hT : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hopen
    have hu : Continuous fun g => Formalism.MainNotions.LocalSituation.liftQ LA _ (s g) :=
      (hs.1.comp (Formalism.MainNotions.LocalSituation.liftQ LA _)).continuous
    have hc : Continuous (swapF LA m ϖ r s (d : G → A'.V)) :=
      continuous_const.mul ((IsModuleTopology.continuous_bilinear_of_finite_left m).comp
        (hu.prodMk d.2.1.1))
    exact Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hT _ hc
  have hD : ReciprocityTheory.Def.d1 (repD L1) Fq ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := ⟨Fq, hFq, rfl⟩
  have heq : (fun x => (Submodule.Quotient.mk
      (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) x) : LL ⧸ L1.T)) =
      -((fun x => (Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
        (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) x) : LL ⧸ L1.T)) +
          ReciprocityTheory.Def.d1 (repD L1) Fq) := by
    funext x
    obtain ⟨g, h⟩ := x
    obtain ⟨e, he⟩ := key g h
    show (Submodule.Quotient.mk (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) (g, h)) :
        LL ⧸ L1.T) = -(Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
          (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) (g, h)) +
        (Submodule.Quotient.mk (((cycLL PD LL g : LLˣ) : LL) * swapF LA m ϖ r s (d : G → A'.V) h)
          - Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) (g * h))
          + Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)))
    rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← add_assoc, he,
      Submodule.Quotient.mk_eq_zero, hL1]
    exact ⟨e, rfl⟩
  unfold CobO
  rw [heq, neg_mem_iff, Submodule.add_mem_iff_left _ hD]

end Cob

theorem cobO_cupQ_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm ϖ r hI s hs d
  obtain ⟨-, -, -, htr, hopen⟩ := hO
  haveI := htr
  exact cobO_swap (P.PD K) hopen L1 hL1 LA LA' m hm ϖ r hI s hs d

end GlobalTheory.BKSwapCup
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algHom_self (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F) (c : ↥F) :
    ‖((σ c : ↥F) : Om l)‖ = ‖(c : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  have h1 := minpoly.algHom_eq F.val F.val.injective (σ c)
  have h2 := minpoly.algHom_eq F.val F.val.injective c
  have h3 := minpoly.algHom_eq σ σ.injective c
  simp only [IntermediateField.coe_val] at h1 h2
  exact congrArg spectralValue (h1.trans (h3.trans h2.symm))

theorem norm_l_pow_lt_one {j : ℕ} (hj : 1 ≤ j) : ‖(l : Om l) ^ j‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (by omega)
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_sub_pow_mul_algHom (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F)
    {j : ℕ} (hj : 1 ≤ j) (d : ↥F) :
    ‖((d - (l : ↥F) ^ j * σ d : ↥F) : Om l)‖ = ‖(d : Om l)‖ := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < ‖(d : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast hd)
  have hlt : ‖-((l : Om l) ^ j * ((σ d : ↥F) : Om l))‖ < ‖(d : Om l)‖ := by
    rw [norm_neg, norm_mul, norm_algHom_self]
    exact mul_lt_of_lt_one_left hd' (norm_l_pow_lt_one hj)
  have e : ((d - (l : ↥F) ^ j * σ d : ↥F) : Om l) =
      (d : Om l) + -((l : Om l) ^ j * ((σ d : ↥F) : Om l)) := by
    push_cast
    ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

theorem frK_isometric_and_one_sub_surjective (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 →
      ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  refine ⟨norm_algHom_self _ _, fun j hj c hc => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  let T : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    LinearMap.id - (LinearMap.mulLeft ℚ_[l] ((l : ↥(K0 K)) ^ j)).comp (frK P K).toLinearMap
  have hT : ∀ d, T d = d - (l : ↥(K0 K)) ^ j * frK P K d := fun d => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro d hd
    have := norm_sub_pow_mul_algHom _ (frK P K) hj d
    rw [← hT, hd] at this
    have h0 : (d : Om l) = 0 := by
      rw [← norm_eq_zero, ← this]; simp
    exact_mod_cast h0
  obtain ⟨d, hd⟩ := LinearMap.injective_iff_surjective.1 hinj c
  rw [hT] at hd
  refine ⟨d, ?_, hd⟩
  rw [← norm_sub_pow_mul_algHom _ (frK P K) hj d, hd]
  exact hc

end GlobalTheory.ExpImage
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.LevelSums

theorem sum_class {R : Type*} [CommRing R] (x : R) (m k n : ℕ) (hm : 0 < m) :
    ∑ a ∈ Finset.range (m * k), (if a % m = n % m then x ^ a else 0) =
      x ^ (n % m) * ∑ i ∈ Finset.range k, (x ^ m) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_eq_single (n % m)]
    · rw [if_pos (by simp), pow_add, pow_mul, mul_comm]
    · intro b hb hne
      rw [if_neg]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
      exact hne
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hm)) h


open Classical in
theorem sum_ind {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 0 < l) (x : R) (s j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (hx : x ^ l ^ s = 1) :
    ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      if x ^ l ^ j = 1 then (l : R) ^ (s - j) * x ^ n else 0 := by
  have hs : l ^ s = l ^ j * l ^ (s - j) := by rw [← pow_add]; congr 1; omega
  have h1 : ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      ∑ a ∈ Finset.range (l ^ j * l ^ (s - j)), (if a % l ^ j = n % l ^ j then x ^ a else 0) := by
    rw [← hs]
    unfold primeTo
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a % l ^ j = n % l ^ j
    · have : ¬ l ∣ a := by
        intro ha
        have hd : l ∣ l ^ j := dvd_pow_self l (by omega)
        exact hn (((Nat.ModEq.of_dvd hd h).dvd_iff dvd_rfl).1 ha)
      simp [h, this]
    · simp [h]
  rw [h1, sum_class x _ _ n (pow_pos hl j)]
  split_ifs with h
  · rw [h, ← pow_eq_pow_mod n h]
    simp [mul_comm]
  · have h2 : (x ^ l ^ j) ^ l ^ (s - j) = 1 := by rw [← pow_mul, ← hs, hx]
    have h3 := mul_geom_sum (x ^ l ^ j) (l ^ (s - j))
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · rw [h4, mul_zero]

theorem pow_shift {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (i j : ℕ) : ζ (i + j) ^ l ^ j = ζ i := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem pow_eq_one_iff_le {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1)
    (h : ∀ j, ζ (j + 1) ^ l = ζ j) (i j : ℕ) : ζ i ^ l ^ j = 1 ↔ i ≤ j := by
  constructor
  · intro hij
    by_contra hlt
    obtain ⟨d, rfl⟩ : ∃ d, i = 1 + (j + d) := ⟨i - 1 - j, by omega⟩
    apply h1
    rw [← pow_shift l ζ h 1 (j + d), pow_add, pow_mul, hij, one_pow]
  · intro hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := pow_shift l ζ h 0 i
    rw [zero_add] at this
    rw [pow_add, pow_mul, this, h0, one_pow]

theorem exists_weights : ∀ (l : ℕ) [Fact l.Prime] (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s j n : ℕ, 1 ≤ j → j ≤ s → ¬ l ∣ n → ∃ lam : ℕ → ℤ, (∑ a ∈ primeTo l s, lam a = if j = 1 then (l : ℤ) ^ (s - 1) else 0) ∧ ∀ i, 1 ≤ i → i ≤ s → ∑ a ∈ primeTo l s, (lam a : Om l) * ζ i ^ a = if i = j then (l : Om l) ^ (if j = 1 then s - 1 else s - j + 1) * ζ j ^ n else 0 := by
  intro l hl ζ h0 h1 h s j n hj hjs hn
  have hl0 : 0 < l := hl.out.pos
  have hz : ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (if a % l ^ j = n % l ^ j then 1 else 0 : ℤ) = (l : ℤ) ^ (s - j) := by
    intro j hj hjs
    simpa using sum_ind l hl0 (1 : ℤ) s j n hj hjs hn (one_pow _)
  have hv : ∀ i, i ≤ s → ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : Om l) * ζ i ^ a =
        if i ≤ j then (l : Om l) ^ (s - j) * ζ i ^ n else 0 := by
    intro i hi j hj hjs
    rw [sum_ind l hl0 (ζ i) s j n hj hjs hn ((pow_eq_one_iff_le l ζ h0 h1 h i s).2 hi)]
    simp only [pow_eq_one_iff_le l ζ h0 h1 h]
  by_cases hj1 : j = 1
  · subst hj1
    refine ⟨fun a => if a % l ^ 1 = n % l ^ 1 then 1 else 0, ?_, fun i hi his => ?_⟩
    · rw [hz 1 le_rfl hjs, if_pos rfl]
    · rw [hv i his 1 le_rfl hjs]
      by_cases e : i = 1
      · subst e; simp
      · rw [if_neg (by omega), if_neg e]
  · have hsj : s - (j - 1) = s - j + 1 := by omega
    refine ⟨fun a => l * (if a % l ^ j = n % l ^ j then 1 else 0) -
      (if a % l ^ (j - 1) = n % l ^ (j - 1) then 1 else 0), ?_, fun i hi his => ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz j hj hjs, hz (j - 1) (by omega) (by omega),
        if_neg hj1, hsj]
      ring
    · simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, mul_assoc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv i his j hj hjs,
        hv i his (j - 1) (by omega) (by omega), if_neg hj1, hsj]
      rcases lt_trichotomy i j with e | e | e
      · rw [if_pos e.le, if_pos (by omega), if_neg e.ne]; ring
      · subst e
        rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg e.ne']; ring

end GlobalTheory.LevelSums
end

section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_Ainf_series_limit (l : ℕ) [Fact l.Prime] (a : ℕ → Ainf l) :
    ∃ x : Ainf l, ∀ n : ℕ, ∃ y : Ainf l,
      x - ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i = ((l : ℕ) : Ainf l) ^ n * y := by
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : Ainf l)}) (Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  have key : ∀ (n : ℕ) (u v : Ainf l),
      u ≡ v [SMOD ((Ideal.span {((l : ℕ) : Ainf l)}) ^ n • ⊤ : Submodule (Ainf l) (Ainf l))] ↔
        ((l : ℕ) : Ainf l) ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨x, hx⟩ := hc.toIsPrecomplete.prec
    (f := fun n => ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi =>
        Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.mp hi).1) _)
  refine ⟨x, fun n => ?_⟩
  have := hx n
  rw [key, ← dvd_neg, neg_sub] at this
  exact this

theorem exists_series_limit_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ)
    (c : ℕ → P.R.BdR) (h0 : ∀ k, c k ∈ FilB P 0)
    (hc : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) :
    ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀,
      b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  choose k hk using hc
  let K : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), k i
  have hK1 : ∀ n, k n ≤ K n := fun n => by
    simp only [K, Finset.sum_range_succ]
    omega
  have hK2 : ∀ n, K n ≤ K (n + 1) := fun n => by
    simp only [K, Finset.sum_range_succ k (n + 1)]
    omega
  have hblock : ∀ n R, K n ≤ R →
      ∑ j ∈ Finset.range R, c j - ∑ j ∈ Finset.range (K n), c j ∈ Lat AI M n := by
    intro n R hR
    rw [← Finset.sum_Ico_eq_sub _ hR]
    exact AddSubgroup.sum_mem _ fun j hj => hk n j ((hK1 n).trans (Finset.mem_Ico.mp hj).1)
  choose a ha using fun n => (mem_Lat AI).mp (hblock n (K (n + 1)) (hK2 n))
  have htel : ∀ n, ∑ j ∈ Finset.range (K n), c j - ∑ j ∈ Finset.range (K 0), c j -
      io AI (∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (ha n)
      rw [Finset.sum_range_succ (fun i => ((l : ℕ) : Ainf l) ^ i * a i), map_add (f := _)]
      convert this using 1
      ring
  obtain ⟨x, hx⟩ := exists_Ainf_series_limit l a
  refine ⟨∑ j ∈ Finset.range (K 0), c j + io AI x,
    add_mem (Submodule.sum_mem _ fun j _ => h0 j) (io_mem AI x), fun n => ⟨K n, fun R hR => ?_⟩⟩
  obtain ⟨y, hy⟩ := hx n
  have h1 := io_mem_Lat AI M n y
  rw [← hy, map_sub] at h1
  have := sub_mem (sub_mem h1 (FilB_le_Lat AI (n := n) (htel n))) (hblock n R hR)
  convert this using 1
  ring

end GlobalTheory.ExpImage
end
end
