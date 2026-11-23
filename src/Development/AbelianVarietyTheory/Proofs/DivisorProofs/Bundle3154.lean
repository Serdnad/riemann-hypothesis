module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefFibre

theorem vAdd_pow' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) :
    vAdd w (x ^ n) = n * vAdd w x := by
  simp [vAdd, map_pow, WithZero.log_pow]

theorem vAdd_one' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem subsingleton_idx : ∀ (N : ℕ) (la : Fin N → ℕ), N = 0 → Subsingleton (Idx la) := by
  rintro N la rfl
  constructor
  rintro ⟨m, -⟩ ⟨m', -⟩
  congr 1
  ext ⟨i, _⟩
  exact i.elim0

theorem dim_eq_one_of_zero {N : ℕ} (la : Fin N → ℕ) (hla : Antitone la) (h : N = 0) : dim la = 1 := by
  haveI := subsingleton_idx N la h
  have h1 := dim_pos hla
  have h2 : dim la ≤ 1 := by rw [dim_eq_card]; exact Fintype.card_le_one_iff_subsingleton.2 inferInstance
  omega

theorem fibreAt_defCase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ →
      ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n c₁ hD hDom hFl Z
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component E H Dw l Xo c r U ξ hD Z
  haveI hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hanti : ∀ τ, Antitone (part Dw a τ) := fun τ i j hij => hDom.1 τ (show (i : ℕ) ≤ j from hij)
  obtain ⟨φ, hinj, hrange, hreads⟩ := GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hconj, hint⟩ := GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hlie, -⟩ := GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree E H Dw l Xo c r U ξ hD Z P
  have hth := GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint E H Dw l Xo c r U ξ hD Z P
  have hIntOne : ∀ (w : HeightOneSpectrum (𝓞 c.F)) (m : ℕ), IntAt w (1 : Matrix (Fin m) (Fin m) c.F) :=
    fun w m i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hBad : ∀ τ, IsAdelic fun w => P.B w τ := fun τ => by
    refine ⟨fun w => (P.loc w).2.1 τ, P.fin.subset fun w hw h => hw ?_⟩
    show IntAt w (P.B w τ) ∧ IntAt w (P.B w τ)⁻¹
    have hB : P.B w τ = 1 := by rw [h.2]; rfl
    rw [hB, inv_one]
    exact ⟨hIntOne w _, hIntOne w _⟩
  have ha0 : ∀ w, P.a w ^ n ≠ 0 := fun w => pow_ne_zero _ (P.loc w).1
  have hsupp1 : (Function.support fun w => vAdd w (P.a w)).Finite :=
    P.fin.subset fun w hw h => hw (by simp only; rw [h.1, vAdd_one'])
  have hsupp : (Function.support fun w => vAdd w (P.a w ^ n)).Finite :=
    hsupp1.subset fun w hw h => hw (by simp only at h ⊢; rw [vAdd_pow', h, mul_zero])
  have hspos : ∀ σ, 0 < (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ =>
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (P.arch σ).1)) n
  have hsconj : ∀ σ, (Real.sqrt (P.N ((starRingEnd ℂ).comp σ)))⁻¹ ^ n = (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ => by
    rw [(hconj σ).1]
  obtain ⟨hdet, hslope⟩ := GlobalTheory.T.slope_dualWeylFibreLattice_ge c.F (E →+* ℂ) Dw.mult (part Dw a) hanti (fun w => P.a w ^ n) P.B
    (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) P.X ha0 hsupp hBad hspos (fun σ τ => (P.arch σ).2.1 τ) hsconj
    (fun σ τ => (hconj σ).2 τ)
  have hlat : IsAdelic fun w => fibA (part Dw a) (P.a w ^ n) (P.B w) :=
    GlobalTheory.T.fibre_action_preserves_adelic_matrices c.F (E →+* ℂ) Dw.mult (part Dw a) (fun w => P.a w ^ n) P.B ha0 hsupp hBad
  have hsec : ∀ x, φ x ∈ sec Xo c a n := fun x => by
    have h1 : φ x ∈ cuspOn U Z (wtZ a n) := hrange ▸ ⟨x, rfl⟩
    have h2 := cuspOn_le U Z (wtZ a n) h1
    rw [cuspW_wtZ] at h2
    exact cusp_le_sec Xo c U a n h2
  have hne : ∀ τ, Nonempty (Idx (part Dw a τ)) := fun τ =>
    Fintype.card_pos_iff.1 ((dim_eq_card _) ▸ dim_pos (hanti τ))

  have hline : lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) (fun w => (vAdd w (P.a w ^ n) : ℝ)) = n * P.degTh := by
    simp only [PtData.degTh, lineDeg, vAdd_pow', Int.cast_mul, Int.cast_natCast, Real.log_pow]
    have hf := fin_mul (ρ := fun w => (vAdd w (P.a w) : ℝ)) (hsupp1.subset fun w hw => by simpa [Function.mem_support] using hw) (lw c.F)
    simp only [mul_assoc]
    rw [← mul_finsum, ← Finset.mul_sum]
    ring

  have hterm : ∀ τ : E →+* ℂ, ¬ τ (H.rt : E) = H.rt0 →
      (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2 = 0 := fun τ hτ => by
    have hm : Dw.mult τ = 0 := by simp [Datum.mult, hτ, hD.q]
    have hm' : (Dw.mult τ : ℝ) = 0 := by rw [hm]; simp
    rw [dim_eq_one_of_zero _ (hanti τ) hm, hm', div_zero, zero_mul]
    simp
  have hpsi : ∀ τ : Psi H,
      (size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) * detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) -
        Real.log (dim (part Dw a τ.1)) / 2 =
      (size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2 := fun τ => by
    have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
    have hl : P.degLie τ.1 = c₁ := by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]
    have hm' : (Dw.mult τ.1 : ℝ) = Dw.p := by rw [hm]
    rw [hm', show detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) = P.degLie τ.1 from rfl, hl]
  have hsum := (Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
    (fun τ => (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2)).symm
  have h0 : ∑ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) = 0 :=
    Finset.sum_eq_zero fun τ _ => hterm τ.1 τ.2
  rw [h0, add_zero] at hsum
  have hsum' : ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) :=
    Finset.sum_congr rfl fun τ _ => hpsi τ
  have hlieSum : ∑ τ : Psi H, P.degLie τ.1 = (Fintype.card (Psi H) : ℝ) * c₁ := by
    rw [Finset.sum_congr rfl fun τ _ => (show P.degLie τ.1 = c₁ by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound : defBound Dw a n c₁ = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
      Real.log (dim (part Dw a τ.1)) / 2) + (Fintype.card (Psi H) : ℝ) * ((n : ℝ) / 2 * c₁) +
      (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) := by
    have hS : ∑ τ : Psi H, ((((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) + (n : ℝ) / 2) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2)) = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2) + ∑ _τ : Psi H, ((n : ℝ) / 2 * c₁) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [defBound, hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hth hn
  rw [hlieSum] at hmul
  refine ⟨TIdx (part Dw a), inferInstance, inferInstance, ⟨fun τ => (hne τ).some⟩, locLat (P.matA a n), P.matY a n, φ,
    GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily c.F _ (P.matA a n) hlat, hdet, ?_, hinj, hrange, fun x hx w v hv =>
      (hint x (φ x) (hsec x) (hreads x)).1 hx w v hv, fun σ x z hz => (hint x (φ x) (hsec x) (hreads x)).2 σ z hz⟩
  refine le_trans ?_ hslope
  have htot : ∑ t : E →+* ℂ, ((size (part Dw a t) : ℝ) / (Dw.mult t : ℝ) *
      detDeg (fun w => P.B w t) (fun σ => P.X σ t) - Real.log (dim (part Dw a t)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) := by
    rw [hsum]
    convert hsum' using 3
  rw [hline, htot, hbound]
  nlinarith [hmul]

end GlobalTheory.DefFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.FieldPt

theorem of_factor {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (V : M.Z.Opens) (v : V.toScheme ⟶ F.X) {T₀ : Scheme.{0}} (ξ : T₀ ⟶ V.toScheme)
    (cO : SiegPre g n ζ ((ξ ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (ξ ≫ V.ι)).obj FinalForm.G ⟶ cO.A))
    (hpbO : SiegPB cO F.univ (ξ ≫ v)) (hmonO : ∀ a, IsMonHom (prO a))
    (hunivO : ∀ (T' : Over T₀) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (ξ ≫ V.ι)).obj FinalForm.G,
      ∀ a, x ≫ prO a = y a)
    (hLO : LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι)))
      (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)))
    (hmatO : ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (ξ ≫ V.ι)).map f))
    {K : Type} [Field K] (t : Sp K ⟶ V.toScheme) (t' : Sp K ⟶ T₀) (ht : t' ≫ ξ = t)
    (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left) (hB : IsGrpPullback B FinalForm.G (t ≫ V.ι) φB) :
    ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧
      (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧
      (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧
      ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left →
        MatEnd pr' a b fB := by
  subst ht
  have hB' : IsGrpPullback B FinalForm.G (t' ≫ (ξ ≫ V.ι)) φB := hB.congr (Category.assoc _ _ _) rfl
  have hφ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (ξ ≫ V.ι) t' hB'
  have hφ'f : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) = φB :=
    pullback.lift_fst _ _ _
  have hφ's : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
      B.hom ≫ t' := pullback.lift_snd _ _ _
  generalize pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) = φ' at hφ hφ'f hφ's
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) _ (Sp K)
    ((ξ ≫ v) ≫ F.s) (((t' ≫ ξ) ≫ v) ≫ F.s) t' rfl (by rw [hid, Category.comp_id]; simp only [Category.assoc])).1 cO
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpbO hc'
  rw [← Category.assoc] at hcomp
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.GrpPullPow.pr_pull prO hφ hχ hmonO hunivO
  refine ⟨c', pr', hcomp, hmon', huniv', ?_, ?_⟩
  · intro L' hL' hiso
    have hL := FinalForm.L.isLB
    have e1 : LBIso (FinalForm.L.L.pull φB) ((FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))).pull φ') := by
      rw [← hφ'f]
      exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame FinalForm.L.L _ _ _ φ' fun _ => rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))) φ' φ' rfl)
        ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB hL _)⟩
    have e2 := LBIso.trans hL' (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hiso e1
    exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull cO.P c'.P _ L' prO pr' W cO.isLB c'.isLB (pull_isLB hL _) hL' hsq hP hpr'
      e2 hLO
  · intro a b f fB hf hfB
    refine GlobalTheory.MatEndPull.matEnd_pull prO pr' a b _ fB hφ hχ hpr' ?_ (hmatO a b f hf)
    apply pullback.hom_ext
    · have e : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.fst FinalForm.G.hom (ξ ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, hφ'f, e, ← Category.assoc, hφ'f, hfB]
    · have w1 : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.snd FinalForm.G.hom (ξ ≫ V.ι) := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, hφ's, w1, hφ's, ← Category.assoc, Over.w fB]

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv K _ t B _ φB hB
  obtain ⟨cO, prO, hpbO, hmonO, hunivO, hLO, hmatO⟩ := GlobalTheory.T.eighth_power_universal_object_at_model_stalk g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
    (t (IsLocalRing.closedPoint K))
  exact of_factor F W FinalForm pr V v _ cO prO hpbO hmonO hunivO hLO hmatO t _
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t) B φB hB

end GlobalTheory.Poinc.Eq8.FieldPt

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegThQF

theorem sharpOver_of_polIso {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {K : Type} [Field K]
    {Q Q' : PolAV (Sp K)} {y : Sp K ⟶ F.X} (φ : Q'.A ≅ Q.A) (hφ : IsPolIso Q' Q φ) (h : GlobalTheory.Poinc.SharpOver F W Q y) :
    GlobalTheory.Poinc.SharpOver F W Q' y := by
  have := hφ.1
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso Q'.L (Q.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ Q Q' y (𝟙 _) φ.hom.left h (isGrpPullback_of_iso φ) h1

theorem finite_sharp (g n : ℕ) (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) :
    Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} :=
  GlobalTheory.T.finite_siegelPoints_e8ThetaPower g n (by omega) F W hW K Q

def ThData {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {K : Type} [Field K] (y : Sp K ⟶ F.X)
    (h m : ℕ) (ze : Γ(Sp K, ⊤)ˣ) (v : (Fin (2 * h) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (Q : PolAV (Sp K)) (hg : Q.g = h) (lev : Out.Level Q (m ^ 2) ze),
    GlobalTheory.Poinc.SharpOver F W Q y ∧ IsThetaPt Q m (levelPoint lev hg) v

theorem finite_thData {g n : ℕ} (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (ℓ h j : ℕ) (hℓ : ℓ.Prime) (ho : Odd ℓ) (hj : 4 ≤ j) (hbig : ((ℓ ^ 2) ^ 2) ^ h * h.factorial < ℓ ^ j)
    (K : Type) [Field K] [IsAlgClosed K] (hl : ((ℓ : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * h) → ZMod ((ℓ ^ j) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ F.X | ThData F W y h (ℓ ^ j) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ F.X, ThData F W y₀ h (ℓ ^ j) ze v
  · obtain ⟨y₀, Q₀, hg₀, lev₀, -, hθ₀⟩ := hne
    refine (finite_sharp g n hn F W hW K Q₀).subset ?_
    rintro y ⟨Q, hg, lev, hS, hθ⟩
    have hN' : ℓ ^ j = ℓ ^ (j - 4) * (ℓ ^ 2) ^ 2 := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    obtain ⟨φ, hφ, -⟩ := (GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion).1 h ℓ 2 (j - 4) ((ℓ ^ 2) ^ 2) (ℓ ^ j)
      hℓ ho le_rfl rfl hN' hbig K hl Q₀ Q hg₀ hg ze lev₀ lev v hθ₀ hθ
    exact sharpOver_of_polIso φ hφ hS
  · exact (Set.finite_empty : (∅ : Set (Sp K ⟶ F.X)).Finite).subset
      (by intro y hy; exact False.elim (hne ⟨y, hy⟩))

theorem finite_fibres : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (g : ℕ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig (ℓ ^ j) f → QFin f := by
  intro ℓ hℓ ho g
  refine ⟨4 + ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial, fun j hj n _ hn3 _ F W hW _ P rig N f hth K _ _ x => ?_⟩
  obtain ⟨hPg, hSh, hrig, hmo, -, hmu, hN, -, hmap⟩ := hth
  have hn : 2 ≤ n := by omega
  have hj4 : 4 ≤ j := by omega
  have hbig : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < ℓ ^ j :=
    lt_of_lt_of_le (by omega : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < j) (Nat.lt_pow_self hℓ.one_lt).le
  obtain ⟨β0, -⟩ := GlobalTheory.ThetaQuasiFinite.exists_spMap (x ≫ F.s)
  have hm0 : ((ℓ ^ j : ℕ) : K) ≠ 0 := by
    have := hmu.map β0
    rw [map_natCast] at this
    exact this.ne_zero
  have hl0 : ((ℓ : ℕ) : K) ≠ 0 := fun h0 => hm0 (by rw [Nat.cast_pow, h0, zero_pow (by omega)])
  have hpos : 0 < (ℓ ^ j) ^ 2 := pow_pos (pow_pos hℓ.pos _) _
  haveI : NeZero (((ℓ ^ j) ^ 2 : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hm0⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((ℓ ^ j) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((ℓ ^ j) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 (cycAway n) K N (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (N + 1) e
  haveI := P.isAb.comm
  haveI : NeZero ((ℓ ^ j) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * (8 * g)) → ZMod ((ℓ ^ j) ^ 2)) → Fin (N + 1)) =>
    finite_thData hn F W hW ℓ (8 * g) j hℓ ho hj4 hbig K hl0 ze
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (N + 1) → K) (d.2 a)))).subset ?_
  intro y hy
  have hy' : y ≫ f = x ≫ f := hy
  obtain ⟨Q, α, hQg, hpb, hQL⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange y P
  have hQg' : Q.g = 8 * g := hQg.trans hPg
  have hfib : PolFib P.A P.L (8 * g) (y ≫ 𝟙 F.X) := ⟨Q, α, hQg', by rwa [Category.comp_id], hQL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ P.A P.L P.isLB (8 * g) K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ P.A P.L rig P.isLB hrig (8 * g) (ℓ ^ j) (N + 1) K _ θ hmo hm0 hN hfib
  have hH : HasTh P.A P.L rig (ℓ ^ j) (y ≫ 𝟙 F.X) cy := ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hmap.1 K y cy hH
  rw [hy'] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 (cycAway n) K N (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := Q.isAb.comm
  obtain ⟨rigQ, hrigQ⟩ := Q.rigid
  have hQ : HasTh Q.A Q.L rigQ (ℓ ^ j) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ P.A P.L rig P.isLB hrig (Sp K) Q.A Q.L rigQ y α Q.isLB hrigQ hpb hQL (ℓ ^ j) (ℓ ^ j)
      (N + 1) (N + 1) K (𝟙 _) cy cy).2 ?_
    simpa only [Category.id_comp, Category.comp_id] using hH
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K Q rigQ (8 * g) (ℓ ^ j) (N + 1) hQg' cy ze hrigQ hmo hm0 hze hQ
  have hSQ : GlobalTheory.Poinc.SharpOver F W Q y := by
    simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ P Q (𝟙 F.X) y α hSh hpb hQL
  exact Set.mem_iUnion.2 ⟨(⟨_, hmuT⟩, β), Q, hQg', lev, hSQ, hβ mu hmu0⟩

end GlobalTheory.SiegThQF
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PreLiftData

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg_data {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)),
      (∀ y, hD.xe y = xe y) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = Φ ∧ hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, fun _ => rfl, rfl, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

theorem exists_rescale_isPullDeg_top : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  intro _ _ _ _ _ _ θ₀ D₀ Q e β hU gp hL hc
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU
  let gg : (TK _).left ⟶ (TW (⊤ : (Sp _).Opens)).left := (jK _ ≫ specOf θ₀) ≫ (Sp _).topIso.inv
  have hg : gg ≫ (⊤ : (Sp _).Opens).ι = jK _ ≫ specOf θ₀ := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec Q.P.A ≫ β = spMap θ₀ ≫ eSec D₀.P.A := (cubeMapOf gp).e_comm
  have hσ : eSec Q.P.A ≫ Q.P.A.hom = 𝟙 _ := Over.w η[Q.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified D₀.P.isLB Q.P.isLB Q.P.A.hom (eSec Q.P.A) hσ w₀ hw₀
    Q.rig Q.rig_gen (φ := eSec D₀.P.A) D₀.rig D₀.rig_gen (spMap θ₀) he
  exact exists_rescale_isPullDeg_data (i := θ₀) D₀ Q ψW gg hg gp w ((isGen_iff w).1 hw) hr e hc

end GlobalTheory.PreLiftData
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  first | exact @GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | exact GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | (intros; apply GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion <;> assumption)
end
