module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  first | exact @GlobalTheory.FrameUnif.princ_finiteIndex | exact GlobalTheory.FrameUnif.princ_finiteIndex | (intros; apply GlobalTheory.FrameUnif.princ_finiteIndex <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_letter_equiv {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  have hf : ∀ s : Σ τ, Fin (m τ), ∃ t : Ψ × Fin r,
      (ρ s.1 ∈ Ψ ∧ t.1.1 = ρ s.1 ∧ (t.2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ t.1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ (t.2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : ρ τ ∈ Ψ
    · have := hp τ h
      exact ⟨(⟨ρ τ, h⟩, ⟨q + i, by omega⟩), Or.inl ⟨h, rfl, rfl⟩⟩
    · have := hq τ h
      have h' : ComplexEmbedding.conjugate (ρ τ) ∈ Ψ := by
        by_contra h'
        exact h ((hΨ _).2 h')
      exact ⟨(⟨_, h'⟩, ⟨q - 1 - i, by omega⟩), Or.inr ⟨h, rfl, rfl, by show (i : ℕ) < q; omega⟩⟩
  choose f hf using hf
  have hext : ∀ s s' : Σ τ, Fin (m τ), ρ s.1 = ρ s'.1 → (s.2 : ℕ) = s'.2 → s = s' := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h1 h2
    obtain rfl : τ = τ' := hρ.1 h1
    obtain rfl : i = i' := Fin.ext h2
    rfl
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [← hss] at h2
    rcases h1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases h2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact hext _ _ (b1.symm.trans b2) (by omega)
    · omega
    · omega
    · refine hext _ _ ?_ (by omega)
      rw [← hcc (ρ s.1), ← b1, b2, hcc]
  · rintro ⟨⟨τ, hτ⟩, j⟩
    have hj := j.2
    by_cases h : (j : ℕ) < q
    · obtain ⟨τ0, h0⟩ := hρ.2 (ComplexEmbedding.conjugate τ)
      have hn : ρ τ0 ∉ Ψ := h0 ▸ (hΨ τ).1 hτ
      have := hq τ0 hn
      refine ⟨⟨τ0, ⟨q - 1 - j, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨q - 1 - j, by omega⟩⟩ with ⟨a, -⟩ | ⟨-, b, c, -⟩
      · exact absurd a hn
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; show ComplexEmbedding.conjugate (ρ τ0) = τ; rw [h0, hcc]
        · rw [c]; show q - 1 - (q - 1 - j) = j; omega
    · obtain ⟨τ0, h0⟩ := hρ.2 τ
      have hn : ρ τ0 ∈ Ψ := h0 ▸ hτ
      have := hp τ0 hn
      refine ⟨⟨τ0, ⟨j - q, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨j - q, by omega⟩⟩ with ⟨-, b, c⟩ | ⟨a, -⟩
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; exact h0
        · rw [c]; show q + (j - q) = j; omega
      · exact absurd hn a

theorem letter_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := F.sig k
  obtain ⟨hp0, hty⟩ := hB.type k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  refine ⟨?_, hp0.trans hq.symm, by rw [hp, hq]; exact hB.rank, ?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_letter_equiv (M.X k).Ψ (M.X k).cmType Dw.p Dw.q r hB.rank (relab c σ) hbij Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, ∀ j,
        (relab c σ (e j).1 ∈ (M.X k).Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
        (relab c σ (e j).1 ∉ (M.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
          ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
    rw [hq]
    refine ⟨idx, fun j => ?_, fun j => ?_, fun x v j => ?_⟩
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), b]
      · rw [if_pos (by omega), b, hcc]
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), c']
      · rw [if_pos (by omega), c']
    · have h := hi j
      generalize idx j = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h ⊢
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dite_eq_left a, dite_eq_left hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ (M.X k).Ψ from hτ), dite_eq_left hn]
        rfl
  · have h := (M.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  · intro τ hτ
    have := hN k τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  · intro φ hφ
    have hrange : LinearMap.range φ = (M.X k).Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact (M.φ k a).2
      · intro hy
        exact ⟨(M.φ k).symm ⟨y, hy⟩, by rw [hφ, LinearEquiv.apply_symm_apply]⟩
    refine ⟨hrange, ?_, ?_, (M.X k).Gm_herm, (M.X k).Gm_det, fun x y => ?_⟩
    · intro a b hab
      rw [hφ, hφ] at hab
      exact (M.φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hrange]
      exact (M.X k).Λ_span
    · rw [hφ, hφ]
      exact hB.ef k x y

end GlobalTheory.FrameUnif
end

section

noncomputable section

namespace GlobalTheory.Frames.SecLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem appLE_bijective {Y Z : Scheme.{0}} (π : Z ⟶ Y) [IsOpenImmersion π] {V : Y.Opens} (hV : V ≤ π.opensRange)
    {V' : Z.Opens} (h : V' ≤ π ⁻¹ᵁ V) (h' : π ⁻¹ᵁ V ≤ V') : Function.Bijective (π.appLE V V' h).hom := by
  obtain rfl : V' = π ⁻¹ᵁ V := le_antisymm h h'
  rw [← Scheme.Hom.app_eq_appLE]
  haveI := π.isIso_app V hV
  exact ConcreteCategory.bijective_of_isIso (π.app V)

theorem exists_pow_mul_eq {Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {M : LB Y} (hM : M.IsLB)
    (U' : M.ι → Z.Opens) (h : ∀ i, U' i ≤ π ⁻¹ᵁ M.U i) (h' : ∀ i, π ⁻¹ᵁ M.U i ≤ U' i) (f : ∀ i, Γ(Z, U' i))
    (hf : ∀ i j, resG Z (inf_le_left : U' i ⊓ U' j ≤ U' i) (f i) =
      (π.appLE (M.U i ⊓ M.U j) (U' i ⊓ U' j) (inf_le_inf (h i) (h j))).hom (M.g i j).val *
        resG Z (inf_le_right : U' i ⊓ U' j ≤ U' j) (f j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ i, (π.appLE _ _ (h i)).hom (s.f i) =
      (π.appLE ⊤ (U' i) le_top).hom a ^ N * f i := by
  have k : ∀ i, U' i ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i) := fun i z hz => ⟨⟨z, rfl⟩, h i hz⟩
  have hb : ∀ i, Function.Bijective (π.appLE _ _ (k i)).hom := fun i =>
    appLE_bijective π inf_le_left (k i) (fun z hz => h' i hz.2)
  choose t ht using fun i => (hb i).2 (f i)
  have hmem : t ∈ secOn M π.opensRange := fun i j => by
    have k₂ : U' i ⊓ U' j ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i ⊓ M.U j) := fun z hz => ⟨k i hz.1, h j hz.2⟩
    apply (appLE_bijective π (inf_le_left.trans inf_le_left) k₂
      (fun z hz => ⟨h' i hz.1.2, h' j hz.2⟩)).1
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    have := hf i j
    rw [← ht i, ← ht j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    exact this
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  obtain ⟨N, u, hu⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M)
    (U := ⊤) isCompact_univ isQuasiSeparated_univ a le_top ha (GlobalTheory.LB.mkSec t hmem)
  let s : LB.Sec M := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord u i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG, GlobalTheory.LB.coord_rel u i j _ _ le_rfl, GlobalTheory.LB.resG_self]⟩
  refine ⟨N, s, fun i => ?_⟩
  have e : resG Y inf_le_left (resG Y le_top a ^ N) * t i =
      resG Y (inf_le_inf_right _ le_top) (GlobalTheory.LB.coord u i) := congrArg (fun w => GlobalTheory.LB.coord w i) hu
  have e₂ := congrArg (π.appLE _ _ (k i)).hom e
  rw [map_mul, ht, map_pow, map_pow, GlobalTheory.LB.resG_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e₂
  exact (GlobalTheory.LB.appLE_resG _ _ _ _).trans e₂.symm

theorem exists_pow_mul_eq_linComb {X Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (e : (fun k => π ≫ φ k) = φ')
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ (N : ℕ) (s : LB.Sec (LB.LinComb L φ ε)), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ π ⁻¹ᵁ (LB.LinComb L φ ε).U j), (π.appLE _ _ hle).hom (s.f j) =
        (π.appLE ⊤ _ le_top).hom a ^ N * s'.f j := by
  subst e
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq π a ha (M := LB.LinComb L φ ε) (LB.isLB_linComb hL φ ε)
    (LB.LinComb L (fun k => π ≫ φ k) ε).U
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) s'.f (fun i j => by
      refine (s'.compat i j).trans (congrArg (· * _) ?_)
      exact congrArg Units.val (DVR.linComb_g_comp φ ε π i j))
  exact ⟨N, s, fun j _ => hs j⟩

theorem opensRange_of_isPullback {S : Type} [CommRing S] (g : S) {Y Z : Scheme.{0}} {π : Z ⟶ Y} {p : Y ⟶ Sp S}
    {p' : Z ⟶ Sp (Localization.Away g)} (h : IsPullback π p' p (spMap (algebraMap S (Localization.Away g))))
    [IsOpenImmersion π] : π.opensRange = Y.basicOpen (p.appTop.hom (toΓ S g)) := by
  have e : Y.basicOpen (p.appTop.hom (toΓ S g)) = p ⁻¹ᵁ PrimeSpectrum.basicOpen g :=
    (Scheme.preimage_basicOpen_top p _).symm.trans (congrArg (p ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := .of S) g))
  rw [e]
  ext y
  have r : Set.range (spMap (algebraMap S (Localization.Away g))) = (PrimeSpectrum.basicOpen g).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have r' := Scheme.Pullback.range_fst p (spMap (algebraMap S (Localization.Away g)))
  rw [r] at r'
  constructor
  · rintro ⟨z, rfl⟩
    have : π z ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) :=
      ⟨h.isoPullback.hom z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
    rw [r'] at this
    exact this
  · intro hy
    have : y ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) := by
      rw [r']; exact hy
    obtain ⟨w, rfl⟩ := this
    exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem appLE_const {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {Y Z : Scheme.{0}} {π : Z ⟶ Y}
    {p : Y ⟶ Sp S} {p' : Z ⟶ Sp T} (w : π ≫ p = p' ≫ spMap φ) (U : Z.Opens) (a : S) :
    (π.appLE ⊤ U le_top).hom (p.appTop.hom (toΓ S a)) = resG Z le_top (p'.appTop.hom (toΓ T (φ a))) := by
  have e₁ : π.appTop.hom (p.appTop.hom (toΓ S a)) = p'.appTop.hom ((spMap φ).appTop.hom (toΓ S a)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, w]
  have e₂ : (spMap φ).appTop.hom (toΓ S a) = toΓ T (φ a) :=
    (congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e₂, ← e₁]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip

theorem isPullback_gxMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) :
    IsPullback (SecPull.gxMap φ x _ rfl) (fst (Over.mk (spMap φ ≫ x)) Xo.univ.t.G).left
      (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) :=
  IsPullback.of_right (by
    convert isPullback_gx (spMap φ ≫ x) using 1
    exact SecPull.gxMap_snd φ x _ rfl) (SecPull.gxMap_fst φ x _ rfl)
    (isPullback_gx x)

theorem exists_secBC_pow_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  intro E _ _ _ H Dw l Xo S _ x g s'
  have hP := isPullback_gxMap (algebraMap S (Localization.Away g)) x
  have hpr : IsProper (fst (Over.mk x) Xo.univ.t.G).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_gx x) Xo.univ.proper
  have : CompactSpace (Over.mk x).left := inferInstanceAs (CompactSpace (Sp S))
  have : QuasiSeparatedSpace (Over.mk x).left := inferInstanceAs (QuasiSeparatedSpace (Sp S))
  have : CompactSpace (Gx x) :=
    QuasiCompact.compactSpace_of_compactSpace (fst (Over.mk x) Xo.univ.t.G).left
  have : QuasiSeparatedSpace (Gx x) :=
    quasiSeparatedSpace_of_quasiSeparated (fst (Over.mk x) Xo.univ.t.G).left
  have hoi : IsOpenImmersion (spMap (algebraMap S (Localization.Away g))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsOpenImmersion (SecPull.gxMap (algebraMap S (Localization.Away g)) x _ rfl) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hoi
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq_linComb _ _ (opensRange_of_isPullback g hP) Xo.univ.t.PP.isLB
    (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap (algebraMap S (Localization.Away g)) ≫ x)) Xo.univ.t.G).left) (fun _ => 1)
    (funext fun _ => SecPull.gxMap_snd _ x _ rfl) s'
  refine ⟨N, s, SecPull.scalSec _ (algebraMap S (Localization.Away g) g ^ N) s',
    ⟨_, SecPull.gxMap_snd _ x _ rfl, SecPull.gxMap_fst _ x _ rfl, fun i h => ?_⟩, fun _ => rfl⟩
  have e₁ : scal x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
  rw [e₁, _root_.one_mul]
  refine (hs i h).trans (congrArg (· * s'.f i) ?_)
  rw [appLE_const _ hP.w]
  simp only [scal, Out.liftFun, map_pow]
  rfl

end GlobalTheory.Frames.SecLoc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordLocal

variable {R : Type} [CommRing R] [IsDomain R]

theorem jK_app_inj (W : (Spec (CommRingCat.of R)).Opens) : Function.Injective ((jK R).app W).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  exact (jK R).app_injective W

omit [IsDomain R] in
theorem toOpen_top_bijective : Function.Bijective (DegPre.toOpen (R := R) ⊤) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective

variable (D : DegPre R) (χ : D.X)

theorem generic_le (j : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hV hy

theorem exists_trans (j j' : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hj : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) (hj' : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j' PUnit.unit))
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (h' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j') :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ, res h ((D.psi χ).s j) = pullU (jK R) V u * res h' ((D.psi χ).s j') := by
  have l : V ≤ (D.c χ).left ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) := fun y hy => ⟨hj hy, hj' hy⟩
  refine ⟨(res l (pullU (D.c χ).left _ (D.P.L.g (j PUnit.unit) (j' PUnit.unit)))) ^ (-1 : ℤ), unit_ext fun y hy => ?_⟩

  have hy' : jK R y ∈ V := hy
  have t := gen_trans (D.psi_gen χ) (𝟙 (TK R).left) y (j := j) (j' := j') (h hy) (h' hy)
  refine (gm_res _ y h hy _).trans (t.trans (Eq.trans ?_ (map_mul _ _ _).symm))
  refine congrArg₂ (· * ·) (Eq.symm ?_) (gm_res _ y h' hy _).symm
  refine (gm_pull (𝟙 _) (jK R) y V hy' _).trans ?_
  rw [Category.id_comp]
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
  refine congrArg (· ^ (-1 : ℤ)) ((gm_res (jK R) y l hy' _).trans ?_)
  refine (gm_pull (jK R) (D.c χ).left y _ (l hy') _).trans ?_
  rw [Category.id_comp]; rfl
theorem psiUnitOn_zero (hB : D.TauBimult) : PsiUnitOn D 0 Set.univ := by
  intro j V hV _ hle h
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
  have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
    Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
  refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
    (Units.isUnit _).map _, fn_ext fun y hy => ?_⟩

  have hy' : jK R y ∈ V := hy
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 (h hy) k)
  have e := PsiZero.val_psi_zero hB hJ
  rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
  refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
    ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
  rw [Category.id_comp]
  refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
  exact congrArg Units.val ((map_inv _ _).trans e.symm)
variable {D χ}

theorem ne_zero_of_coord {r : R} (h : PsiCoord D χ r) : r ≠ 0 := by
  rintro rfl
  obtain ⟨j, -, h, e⟩ := h
  rw [map_zero, map_zero] at e
  have hu := ((D.psi χ).s j).isUnit.map ((TK R).left.presheaf.map (homOfLE h).op).hom
  rw [← e] at hu
  haveI : Nonempty (jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    ⟨⟨closedPoint (FractionRing R), trivial⟩⟩
  exact not_isUnit_zero hu

theorem exists_unit_of_coord {r r' : R} (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : ∃ u : Rˣ, r' = u * r := by
  obtain ⟨j, hj, h, e⟩ := h
  obtain ⟨j', hj', h', e'⟩ := h'
  obtain ⟨u, hu⟩ := exists_trans D χ j' j hj' hj h' h
  let φ := RingEquiv.ofBijective _ (toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, toOpen_top_bijective.1 (jK_app_inj ⊤ ?_)⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e, e']
  exact congrArg Units.val hu

theorem not_mem_of_coord {W : Set (Sp R)} {𝔭 : PrimeSpectrum R} (hW : IsOpen W) (hp : 𝔭 ∈ W) (hU : PsiUnitOn D χ W)
    {r : R} (h : PsiCoord D χ r) : r ∉ 𝔭.asIdeal := by
  obtain ⟨j, hj, h, e⟩ := h
  obtain ⟨V, hV, hpV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of R)) (x := 𝔭)
    (U := ⟨W, hW⟩) hp
  have h₂ : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := le_top.trans hj
  obtain ⟨s, hs, es⟩ := hU j V hV hle h₂ (generic_le D χ j h₂)
  have k : DegPre.toOpen (R := R) V r = s := by
    refine jK_app_inj V (Eq.trans ?_ es.symm)
    refine fn_ext fun y hy => ?_
    have hy' : jK R y ∈ V := hy
    have a := congrArg (gs (𝟙 _) y _) e
    have a₁ := gs_pull (𝟙 _) (jK R) y ⊤ trivial (DegPre.toOpen (R := R) ⊤ r)
    have a₂ := gs_res (𝟙 _) y h trivial ((D.psi χ).s j).val
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_ (gs_res (𝟙 _) y (generic_le D χ j h₂) hy _).symm)
    refine Eq.trans ?_ (a₁.symm.trans (a.trans a₂))
    rw [Category.id_comp]
    exact (gs_res (jK R) y le_top hy' _).trans (gs_res (jK R) y (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤) trivial _).symm
  rw [← k] at hs
  have b := (Spec (CommRingCat.of R)).basicOpen_of_isUnit hs
  have c : (Spec (CommRingCat.of R)).basicOpen (DegPre.toOpen (R := R) V r) =
      V ⊓ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    (Spec (CommRingCat.of R)).basicOpen_res _ _
  rw [b, basicOpen_eq_of_affine] at c
  exact (c.le hpV).2

theorem exists_chart_top [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    ∃ j : PUnit → D.P.L.ι, (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
  obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c χ).left (closedPoint R))
  exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff ((D.c χ).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)), IsIntegrallyClosed R → ∀ χ, (∃ r, PsiCoord Dg.toPre χ r ∧ r ≠ 0 ∧ (χ ≠ 0 → r ∈ maximalIdeal R) ∧ (χ = 0 → IsUnit r)) ∧ (∀ r r', PsiCoord Dg.toPre χ r → PsiCoord Dg.toPre χ r' → ∃ u : Rˣ, r' = u * r) ∧ ∀ (W : Set (Sp R)) (𝔭 : PrimeSpectrum R), IsOpen W → 𝔭 ∈ W → PsiUnitOn Dg.toPre χ W → ∀ r, PsiCoord Dg.toPre χ r → r ∉ 𝔭.asIdeal := by
  intro R _ _ _ _ Dg _ χ
  refine ⟨?_, fun _ _ => exists_unit_of_coord, fun _ _ hW hp hU _ => not_mem_of_coord hW hp hU⟩
  obtain ⟨j, hj⟩ := exists_chart_top Dg.toPre χ
  have h := generic_le Dg.toPre χ j hj
  by_cases hχ : χ = 0
  · subst hχ
    have hU := psiUnitOn_zero Dg.toPre Dg.tau_bimult
    obtain ⟨s, -, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj h
    obtain ⟨r, rfl⟩ := toOpen_top_bijective.2 s
    have hr : PsiCoord Dg.toPre 0 r := ⟨j, hj, h, e⟩
    exact ⟨r, hr, ne_zero_of_coord hr, fun h => absurd rfl h, fun _ =>
      IsLocalRing.notMem_maximalIdeal.1 (not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial hU hr)⟩
  · obtain ⟨s, hs, e⟩ := Dg.psi_pos χ hχ j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    have hr : PsiCoord Dg.toPre χ r := ⟨j, hj, h, e⟩
    exact ⟨r, hr, ne_zero_of_coord hr, fun _ => hm, fun h => absurd h hχ⟩

end GlobalTheory.PsiCoordLocal
end
end
