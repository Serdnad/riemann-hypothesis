module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle011

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_castLE_eq {n : ℕ} (h : n ≤ r) (g : Fin r → ℝ) :
    ∑ a : Fin n, g (Fin.castLE h a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < n), g b := by
  classical
  refine Finset.sum_bij (fun a _ => Fin.castLE h a) (fun a _ => by simp) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun a _ => rfl)

theorem sum_shift_eq {n m : ℕ} (hn : n ≤ r) (hm : m = r - n) (g : Fin r → ℝ) (f : Fin m → Fin r)
    (hf : ∀ a, (f a : ℕ) = n + a) :
    ∑ a : Fin m, g (f a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < n), g b := by
  classical
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Fin.val hab
    rw [hf, hf] at h1
    exact Fin.ext (by omega)
  refine Finset.sum_bij (fun a _ => f a) (fun a _ => by simp [hf]) (fun a _ b _ hab => hinj hab)
    (fun b hb => ?_) (fun a _ => rfl)
  have hb' : ¬ (b : ℕ) < n := by simpa using hb
  refine ⟨⟨b - n, by have := b.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
  rw [hf]
  simp only
  omega

theorem conj_conj_X (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

theorem cols_linInd (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (τ : X.Ψ) :
    LinearIndependent ℂ (X.colP x τ) := by
  have h := A.e_flag τ r le_rfl
  have h1 : (fun a : Fin r => A.e τ (Fin.castLE le_rfl a)) = A.e τ := funext fun a => rfl
  have h2 : (fun a : Fin r => col (mat x τ) (Fin.castLE le_rfl a)) = fun a => col (mat x τ) a :=
    funext fun a => rfl
  rw [h1, h2, e_span X τ (A.e τ) (A.e_orth τ)] at h
  have hcols : LinearIndependent ℂ (fun a : Fin r => col (mat x τ) a) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank h.le (by simp)
  exact hcols.comp _ (Fin.castLE_injective X.p0_le)

theorem norm_sq_eq (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (v : Fin r → E) :
    ‖A.φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
  classical
  have hc : ∀ τ : X.Ψ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
  have hmaj : ∀ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v) =
      ∑ b : Fin r, ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := fun τ =>
    maj_eq_sum X τ (A.e τ) (A.e_orth τ) x (A.e_flag τ X.p0 X.p0_le) (cols_linInd X x A τ) _
  let F : (E →+* ℂ) → ℝ := fun σ => ∑ a : Fin (A.T.dim σ), ‖A.φ v ⟨σ, a⟩‖ ^ 2
  have hpos : ∀ τ : X.Ψ, F τ.1 = X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < X.p0),
      ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hle : A.T.dim τ.1 ≤ r := by rw [A.dim_pos τ]; exact X.p0_le
    have e1 : ∀ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 =
        X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ (Fin.castLE hle a))‖ ^ 2 := by
      intro a
      rw [A.coord_pos τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ)]
    show ∑ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum,
      sum_castLE_eq hle (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2), A.dim_pos τ]
  have hneg : ∀ τ : X.Ψ, F (ComplexEmbedding.conjugate τ.1) =
      X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < X.p0),
        ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hlt : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)), X.p0 + a.1 < r := by
      intro a
      have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (A.dim_neg τ)
      have := X.p0_le
      omega
    have e1 : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
        ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 =
          X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ ⟨X.p0 + a.1, hlt a⟩)‖ ^ 2 := by
      intro a
      rw [A.coord_neg τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ), Complex.norm_conj, norm_neg]
    show ∑ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
      ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum]
    congr 1
    exact sum_shift_eq X.p0_le (A.dim_neg τ) (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2)
      (fun a => ⟨X.p0 + a.1, hlt a⟩) (fun a => rfl)
  have hsplit : ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ ∈ X.Ψ)]
    have hfilt : Finset.univ.filter (fun σ => σ ∈ X.Ψ) = X.Ψ := by ext; simp
    have hcomp : ∑ σ ∈ Finset.univ.filter (fun σ => σ ∉ X.Ψ), F σ =
        ∑ τ ∈ X.Ψ, F (ComplexEmbedding.conjugate τ) := by
      refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
        (fun τ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        rw [X.cmType, conj_conj_X]
        exact hσ
      · intro τ hτ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        exact (X.cmType τ).mp hτ
      · intro σ _; exact conj_conj_X σ
      · intro τ _; exact conj_conj_X τ
      · intro σ _; rw [conj_conj_X]
    rw [hfilt, hcomp, ← Finset.sum_add_distrib,
      ← Finset.sum_coe_sort X.Ψ (fun σ => F σ + F (ComplexEmbedding.conjugate σ))]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  show ∑ σ, F σ = _
  rw [hsplit]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hpos τ, hneg τ, hmaj τ, ← mul_add, Finset.sum_filter_add_sum_filter_not]

theorem torusAtIs_holds : TorusAtIsStatement := by
  intro E _ _ _ r X x A
  exact ⟨A.φ, A.sg, A.sg_pm, A.lat, A.act_eq, fun v _ => norm_sq_eq X x A v, A.im_eq⟩

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf

open NumberField

noncomputable section

theorem torusAtLa1_holds : TorusAtLa1Statement := by
  intro E _ _ _ r X x hx T hT
  obtain ⟨φ, s, -, hL, -, hnorm, -⟩ := hT
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
    positivity
  have hmaj : ∀ (τ : X.Ψ) (w : Fin r → ℂ), 0 ≤ X.maj x τ w := fun τ w => by
    rcases eq_or_ne w 0 with rfl | h
    · simp [ReciprocityTheory.ChartRestriction.G.FD.Data.maj, ReciprocityTheory.ChartRestriction.G.FD.Data.posPart, ReciprocityTheory.ChartRestriction.G.FD.hermC]
    · exact (X.maj_pos hx τ h).le
  obtain ⟨τ0⟩ : Nonempty X.Ψ :=
    Fintype.card_pos_iff.1 (ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos (X := X))
  have hpos : ∀ v ∈ X.Λ, v ≠ 0 →
      0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := by
    intro v _ hv0
    have hne : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
      intro h
      exact (map_ne_zero τ0.1).2 ha (congrFun h a)
    exact Finset.sum_pos' (fun τ _ => mul_nonneg (hc τ).le (hmaj τ _))
      ⟨τ0, Finset.mem_univ _, mul_pos (hc τ0) (X.maj_pos hx τ0 hne)⟩
  have hset : {t : ℝ | ∃ y ∈ T.L, y ≠ 0 ∧ t = ‖y‖} = Real.sqrt '' {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧
      t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} := by
    ext t
    constructor
    · rintro ⟨y, hy, hy0, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (hL y).1 hy
      have hv0 : v ≠ 0 := by rintro rfl; exact hy0 (map_zero φ)
      exact ⟨_, ⟨v, hv, hv0, rfl⟩, by rw [← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]⟩
    · rintro ⟨_, ⟨v, hv, hv0, rfl⟩, rfl⟩
      refine ⟨φ v, (hL _).2 ⟨v, hv, rfl⟩, fun h => ?_, ?_⟩
      · have h1 := hnorm v hv
        rw [h, norm_zero] at h1
        linarith [hpos v hv hv0]
      · rw [← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]
  have hla : T.la1 = X.la1 x := by
    unfold PT.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    rw [hset]
    rcases Set.eq_empty_or_nonempty {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧
        t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} with hS | hS
    · rw [hS]
      simp
    · refine (Monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt
        (fun a b h => Real.sqrt_le_sqrt h) hS ⟨0, ?_⟩).symm
      rintro _ ⟨v, _, _, rfl⟩
      exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hmaj τ _)
  refine ⟨hla, fun th => ?_⟩
  simp only [PT.ph, phiFD, hla]

end

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def partSub {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

variable {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

lemma sep_X (hI : IsSplit P I) : ∀ g ∈ Xg X.L I, g ≠ 0 → 1 ≤ ‖g‖ := by
  intro g hg hg0
  obtain ⟨x, hx, hu⟩ := hg
  have h1 := hI.sep x hx g hu hg0
  have h2 : (1:ℝ) ≤ ‖g‖ ^ 2 := P.C2.trans h1
  nlinarith [norm_nonneg g]

lemma exists_short_real_span (hI : IsSplit P I) : ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
    Submodule.span ℝ (Set.range u) = IR I ∧
    ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
  obtain ⟨x, u, hxu, hli, hb⟩ := hI.u1
  refine ⟨x, u, hxu, ?_, hb⟩
  have hle : Submodule.span ℝ (Set.range u) ≤ IR I := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hxu j).2.1
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

lemma span_inf_partSub_le {σ : E →+* ℂ} (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : ∀ j, prj σ (u j) ∈ W) :
    ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ W := by
  rintro v ⟨hvI, hvσ⟩
  have hvσ' : ∀ j : Idx X.dim, j.1 ≠ σ → v j = 0 := hvσ
  have hfix : prj σ v = v := by
    ext i
    by_cases h : i.1 = σ
    · simp [prj, h]
    · simp [prj, h, hvσ' i h]
  have hspan : Submodule.span ℂ (I : Set (Vsp X.dim)) ≤ Submodule.span ℂ (Set.range u) := by
    rw [Submodule.span_le]
    intro y hy
    have hyR : y ∈ IR I := Submodule.subset_span hy
    rw [← hu] at hyR
    exact Submodule.span_le_restrictScalars ℝ ℂ (Set.range u) hyR
  have hv : v ∈ Submodule.span ℂ (Set.range u) := hspan hvI
  rw [← hfix]
  have hmap : Submodule.map (prj σ) (Submodule.span ℂ (Set.range u)) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hW j
  exact hmap (Submodule.mem_map_of_mem hv)

lemma exists_out {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ)
    (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : Module.finrank ℂ W < ρ) : ∃ j, prj σ (u j) ∉ W := by
  by_contra hcon
  push_neg at hcon
  have hle := span_inf_partSub_le u hu W hcon
  have h2 : Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ :
      Submodule ℂ (Vsp X.dim))) ≤ Module.finrank ℂ W := Submodule.finrank_mono hle
  rw [hρ] at h2
  omega

lemma rho_le [IsCMField E] (hI : IsSplit P I) (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ) :
    ρ ≤ P.m := by
  classical
  obtain ⟨x, u, hxu, hspan, -⟩ := exists_short_real_span hI
  set S := prj σ '' (Xg X.L I : Set (Vsp X.dim))
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hV1 : ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ Submodule.span ℂ b := by
    rw [hbspan]
    exact span_inf_partSub_le u hspan _ fun j => Submodule.subset_span ⟨u j, ⟨x j, (hxu j).1, (hxu j).2⟩, rfl⟩
  have h1 : ρ ≤ Fintype.card b := by
    have := Submodule.finrank_mono hV1
    rw [hρ] at this
    have h2 := finrank_span_eq_card hbli
    rw [Subtype.range_coe] at h2
    have h3 : Fintype.card {x // x ∈ b} = Fintype.card b := Fintype.card_congr (Equiv.refl _)
    omega
  have h2 := rank_bound X.L I (sep_X hI) (fun α u hu => Xg_act X.stable hI.stable α hu) ω hω σ b hbS hbli
  obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf : 2 * PT.f E ≤ Module.finrank ℚ E := by unfold PT.f; omega
  have h3 : Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℚ E * ρ' := by
    rw [hρ'] at h2; nlinarith
  have h4 := Nat.le_of_mul_le_mul_left h3 hn
  omega

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem lemmaN (_hd : DimStatement) : NStatement := thetaBasis_holds

end ReciprocityTheory.ChartRestriction.G.I2
end
