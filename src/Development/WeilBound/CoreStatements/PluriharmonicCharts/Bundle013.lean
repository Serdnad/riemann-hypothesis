module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle017
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_blockpos

theorem posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1, hB.1]; simp
  · have e : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 B *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [e]
    have h1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
      by_cases h : x ∘ Sum.inl = 0
      · rw [h]; simp
      · exact (hA.2 h).le
    have h2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      by_cases h : x ∘ Sum.inr = 0
      · rw [h]; simp
      · exact (hB.2 h).le
    by_cases h : x ∘ Sum.inl = 0
    · have h' : x ∘ Sum.inr ≠ 0 := fun h' => hx (funext fun i => by
        rcases i with i | i
        · exact congrFun h i
        · exact congrFun h' i)
      exact add_pos_of_nonneg_of_pos h1 (hB.2 h')
    · exact add_pos_of_pos_of_nonneg (hA.2 h) h2

end PositivityTheory.Xgp.c_bm_exists_blockpos

theorem PositivityTheory.Xgp.t_c_bm_exists_blockpos : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  intro p q Γ h
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
    simp only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab
    · rfl
    · rfl
    · exact absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab
  · refine Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective
    exact PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks
      (h.submatrix (omEmb_strictMono p q).injective).transpose.inv
      (h.submatrix (wEmb_strictMono p q).injective)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem det_head {p q k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (M : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (f : I → Fin q ⊕ Fin p) (hf : Function.Injective f)
    (hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x) :
    (M.submatrix (Subtype.val : {a : Fin (p + q) // (a : ℕ) < k} → _) Subtype.val).det =
      ((M.submatrix (blockEquiv p q) (blockEquiv p q)).submatrix f f).det := by
  let e : I ≃ {a : Fin (p + q) // (a : ℕ) < k} := Equiv.ofBijective
    (fun i => ⟨blockEquiv p q (f i), (hr _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf ((blockEquiv p q).injective (congrArg Subtype.val h)), fun ⟨a, ha⟩ => by
      obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
      obtain ⟨i, rfl⟩ := (hr x).1 ha
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sub_conj {m I : Type} [Fintype m] (H Y : Matrix m m ℂ) (f : I → m) :
    (Hᴴ * Y * H).submatrix f f = (H.submatrix id f)ᴴ * Y * H.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

theorem periodGram_of {p q : ℕ} (Pi : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ)
    (Gw : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin q) (Fin p) ℂ) (hGo : Go.PosDef) (hdet : IsUnit Pi.det)
    (h : (gramOf (sigForm (p + q) p) Pi).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) :
    IsPeriodGram p Pi ((fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  classical
  refine ⟨⟨hdet, ?_⟩, fun h' hb k => ?_⟩
  · let f : {a : Fin (p + q) // (a : ℕ) < p + q - p} → Fin q := fun a => ⟨a.1, by have := a.2; omega⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (Fin.ext (congrArg Fin.val e :))
    convert hGo.submatrix hf using 1
    ext a b
    have := congrFun (congrFun h (.inl (f a))) (.inl (f b))
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply] at this
    simp at this
    simp only [gramHead, Matrix.neg_apply, Matrix.submatrix_apply]
    rw [neg_eq_iff_eq_neg]
    exact this
  have e1 : (gramOf (sigForm (p + q) p) (Pi * h')).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← h, ← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (h'ᴴ * (fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm * h').submatrix
      (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q),
      ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q)]
    simp
  unfold gramHead
  by_cases hk : q ≤ k
  · let f : Fin q ⊕ {b : Fin p // q + (b : ℕ) < k} → Fin q ⊕ Fin p := Sum.map id Subtype.val
    have hf : Function.Injective f := Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => by show (a : ℕ) < k; omega⟩
      · refine ⟨fun h => ⟨.inr ⟨b, h⟩, rfl⟩, ?_⟩
        rintro ⟨a | a, ha⟩
        · simp [f] at ha
        · obtain rfl : a.1 = b := by simpa [f] using ha
          exact a.2
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₂ : Matrix (Fin p) {b : Fin p // q + (b : ℕ) < k} ℂ := (wBlock h').submatrix id Subtype.val
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromBlocks (omBlock h') 0 0 h₂ := by
      ext (a | a) (b | b) <;> rfl
    rw [e3]
    have e4 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') (Z * h₂) 0 1)ᴴ * fromBlocks (-Go) 0 0 (h₂ᴴ * Gw * h₂) *
          fromBlocks (omBlock h') (Z * h₂) 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    have e5 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') 0 0 1)ᴴ * fromBlocks Go 0 0 (h₂ᴴ * Gw * h₂) * fromBlocks (omBlock h') 0 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    rw [e4, e5]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · let f : {a : Fin q // (a : ℕ) < k} → Fin q ⊕ Fin p := fun a => .inl a.1
    have hf : Function.Injective f := fun a b e => Subtype.ext (Sum.inl_injective e)
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · refine ⟨fun h => ⟨⟨a, h⟩, rfl⟩, ?_⟩
        rintro ⟨b, hb⟩
        obtain rfl : b.1 = a := Sum.inl_injective hb
        exact b.2
      · refine ⟨fun h => absurd h (by show ¬ q + (b : ℕ) < k; omega), ?_⟩
        rintro ⟨a, ha⟩
        simp [f] at ha
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₁ : Matrix (Fin q) {a : Fin q // (a : ℕ) < k} ℂ := (omBlock h').submatrix id Subtype.val
    set O : Matrix (Fin p) {a : Fin q // (a : ℕ) < k} ℂ := 0 with hO
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromRows h₁ O := by
      ext (a | a) b <;> rfl
    rw [e3]
    have e4 : (fromRows h₁ O)ᴴ * ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromRows h₁ O = -((fromRows h₁ O)ᴴ * fromBlocks Go 0 0 Gw * fromRows h₁ O) := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [hO]
    rw [e4, Matrix.det_neg]
    simp

theorem periodGram_conj {N j : ℕ} {Pi G : Matrix (Fin N) (Fin N) ℂ} (h : IsPeriodGram j Pi G) :
    IsPeriodGram j (Pi.map (starRingEnd ℂ)) (G.map (starRingEnd ℂ)) := by
  classical
  have g : ∀ (k : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), gramHead (sigForm N j) k (X.map (starRingEnd ℂ)) =
      (gramHead (sigForm N j) k X).map (starRingEnd ℂ) := fun k X => by
    ext a b
    simp [gramHead, gramOf, Matrix.mul_apply, Matrix.diagonal_apply, apply_ite]
  have dm : ∀ {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ),
      (X.map (starRingEnd ℂ)).det = starRingEnd ℂ X.det := fun X => (RingHom.map_det _ X).symm
  refine ⟨⟨?_, ?_⟩, fun h' hb k => ?_⟩
  · rw [dm]; exact h.1.1.map _
  · rw [g]
    suffices e : -(gramHead (sigForm N j) (N - j) Pi).map (starRingEnd ℂ) = (-gramHead (sigForm N j) (N - j) Pi)ᵀ by
      rw [e]; exact h.1.2.transpose
    ext a b
    have := h.1.2.isHermitian.apply a b
    simp only [Matrix.neg_apply, star_neg, neg_inj] at this
    simp only [Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, neg_inj]
    rw [← this]; simp
  · have := h.2 (h'.map (starRingEnd ℂ)) (fun a b hab => by simp [hb a b hab]) k
    have e1 : Pi.map (starRingEnd ℂ) * h' = (Pi * h'.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    have e2 : (h'ᴴ * G.map (starRingEnd ℂ) * h').submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) = (((h'.map (starRingEnd ℂ))ᴴ * G * h'.map (starRingEnd ℂ)).submatrix
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    rw [e1, g, e2, dm, dm, Complex.norm_conj, Complex.norm_conj, this]

theorem blockG_conj {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    have e1 : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ = (omBlock Γ)ᴴ := rfl
    rw [e1, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv]
    rfl
  ext a b
  simp only [blockG, e, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (blockEquiv p q).symm a with a | a <;> rcases (blockEquiv p q).symm b with b | b <;>
    simp [wBlock]

end PositivityTheory.Xgp.c_bm_exists_period
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem PositivityTheory.Xgp.isFrameAt_comap_gbS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (q : Cpt 𝔐.ξ), M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → (Lat.comap (fun p => 𝔐.V (.inl τ) p ⊔ 𝔐.V (.inr τ) p) (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype).IsFrameAt (gbS tie F τ) q := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie F hF τ q hq
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω _ _ M.x 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen (.inr τ)) (𝔐.Vgen (.inl τ)) := hind.pairwiseDisjoint Sum.inr_ne_inl
  have hW : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q := tie.frameW q F hF hq τ
  obtain ⟨hex, hall⟩ := omBundle_dualFrame 𝔐 τ q (tie.frameO q F hF hq τ)
  have hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
    have hex' : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 := hex
    unfold dualFam
    rw [dite_eq_left hex']
    exact hex'.choose_spec
  have hO := hall _ hd
  have e : (fun i => (gbS tie F τ i : 𝔐.Li)) =
      Sum.elim (fun b => (dualFam tie F τ b : 𝔐.Li)) (tie.wFrame F τ) ∘ (blockEquiv D.p D.q).symm := by
    funext i
    simp only [gbS, Function.comp]
    rcases (blockEquiv D.p D.q).symm i with a | a <;> rfl
  constructor
  · refine LinearIndependent.of_comp (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype ?_
    show LinearIndependent M.Ω (fun i => (gbS tie F τ i : 𝔐.Li))
    rw [e]
    refine (hO.1.sum_type hW.1 (hdisj.mono ?_ ?_)).comp _ (blockEquiv D.p D.q).symm.injective
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact (dualFam tie F τ b).2)
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact wFrame_mem tie F τ b)
  · have h1 : 𝔐.V (.inl τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range (tie.wFrame F τ)) := hW.2
    have h2 : 𝔐.V (.inr τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range fun b => (dualFam tie F τ b : 𝔐.Li)) := hO.2
    show (𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q).comap
      ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    have hinj : Function.Injective
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) :=
      (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).injective_subtype
    have e' : 𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q = (Submodule.span (regAt 𝔐.ξ q) (Set.range (gbS tie F τ))).map
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) := by
      rw [Submodule.map_span, ← Set.range_comp, h1, h2, ← Submodule.span_union, Set.union_comm, ← Set.Sum.elim_range]
      congr 1
      refine Eq.trans ?_ (congrArg Set.range e.symm)
      exact ((blockEquiv D.p D.q).symm.surjective.range_comp _).symm
    rw [e', Submodule.comap_map_eq_of_injective hinj]
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_fl_arith : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
  intro Ψ _ _ _ N hN
  have h := FlagArithVar.proof Ψ N hN
  rwa [dimFl, ← Nat.choose_two_right] at h
end
