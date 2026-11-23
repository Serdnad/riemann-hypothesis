module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

abbrev cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : IrrRep (GL (Fin n) k)) : IrrGL (k := k) := ⟨n, π.cl⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def sumList (l : List (WD h)) : WD h := l.foldr WD.lpSum (WD.lpZero (h := h))

def IsIrrWD (x : WD h) : Prop := ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

def IsTameWD (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧
    ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1

structure Laws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (ε E w h ψ ((rc (cls π)).lpChar (rc (cls τ))))

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep →
    rc x = sumList (l.map fun Δ =>
      ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))

  det : ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) =
    sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j))

  prod : ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E)))
    (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) →
    rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ))

  supp : ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s →
    ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod

  sph : ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr

  sat : ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹)

  depth : ∀ x : IrrGL (k := w.adicCompletion E),
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x)

variable (h) in
def IsRec (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), IsDeligneEps ε ∧ Laws a ha ε rc

def FieldCompatible {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

end GlobalTheory.LocLanglands

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsGL : Prop :=
  (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃! rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc) ∧
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'),
    IsRec h rc → IsRec h' rc' → FieldCompatible rc rc'

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpOfChar (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) :
    x.lpChar (WD.lpOfChar h ξ hξ) = x.lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpOfChar, WD.lpChar_mk, WD.lpTwist_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [smul_smul, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]


variable (w) in
theorem resCard_eq_normV : resCard (w.adicCompletion E) = normV w := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : resCard (w.adicCompletion E) = Formalism.UG.qV E w := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  simpa only [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq

variable {a : Weil h →* (w.adicCompletion E)ˣ}

theorem IsLocalArtin.unrChar_comp (ha : IsLocalArtin h a) (c : ℂˣ) :
    (SmGL.unrChar (w.adicCompletion E) c).comp a = WeilDeligne.unrChar h c⁻¹ := by
  refine MonoidHom.ext fun σ => ?_
  rw [MonoidHom.comp_apply, SmGL.unrChar_apply, ha.ord_eq, WeilDeligne.unrChar_apply, _root_.zpow_neg, _root_.inv_zpow]

theorem IsLocalArtin.absPow_comp (ha : IsLocalArtin h a) (s : ℝ) :
    (absPow (w.adicCompletion E) s).comp a = WeilDeligne.unrChar h (qPow w s) := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [MonoidHom.comp_apply, val_absPow_ofReal, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV,
    WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, coe_qPow, ← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm,
    Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]

variable {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem Laws.tw_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  rw [H.twist, H.one, lpChar_lpOfChar]

theorem Laws.nu_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.tw_eq, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem Laws.eq_iff (H : Laws a ha ε rc) {n : ℕ} (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))) :
    rc (cls π) = rc (cls π') ↔ Nonempty (π.ρ.Equiv π'.ρ) :=
  H.bij.1.eq_iff.trans (IrrGL.of_eq_of (π := π.ρ) (σ := π'.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π'.smooth)
    (hi' := π'.irr))

end GlobalTheory.LocLanglands
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.Published.CoverSeries

variable {p q n : ℕ}

def pull {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : URep T where
  H := H
  π := { toFun := fun x => σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))
         map_one' := by simpa using hσ.1.1
         map_mul' := fun x y => by
           rw [ContinuousLinearMap.mul_def, ← hσ.1.2 _ (h.cov_mem T x) _ (h.cov_mem T y)]
           simp [Matrix.submatrix_mul_equiv] }
  isom x v := hσ.2.1 _ (h.cov_mem T x) v
  cont v := (hσ.2.2 v).comp_continuous
    ((Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)).matrix_reindex e e) (h.cov_mem T)

theorem exists_of_isDSPar (T : GrpData p q)
    (hM : ∀ U : URep T, Formalism.MainNotions.SchurIrreducible.IrrU U → ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io)
    (P : SignedPar n) {e : Ix p q ≃ Fin n} (h : BlockOrd e P.sgn) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDSPar P σ) :
    ∃ R : DSRep T, HasParam R (blockPar P e) := by
  haveI : CompleteSpace H := hσ.1
  have hU := hσ.2.2.1
  have hirr : Formalism.MainNotions.SchurIrreducible.IrrU (pull h T hU) := ⟨hσ.2.1, fun S hS hst => hσ.2.2.2.1 S hS fun g hg v hv => by
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    exact hst x v hv⟩
  obtain ⟨M, io, m1, m2, m3⟩ := hM _ hirr
  haveI := SqInt.isHaarMeasure_map_covU h T
  have hμ := Measure.isMulLeftInvariant_eq_smul (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn)
  obtain ⟨d, hd, hI⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n P.sgn P.lam H σ hσ _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn))
  refine ⟨⟨pull h T hU, hirr.1, hirr.2, d, hd, fun x y => ?_, M, io, m1, m2, m3⟩, ?_⟩
  · change H at x y
    obtain ⟨i1, i2⟩ := hI x y x y
    rw [← ENNReal.smul_def, ← hμ] at i1 i2
    have hf : (fun g => coefOn (ε := P.sgn) σ x y g * star (coefOn (ε := P.sgn) σ x y g)) =
        fun g => ((‖coefOn (ε := P.sgn) σ x y g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hf] at i1 i2
    have hm := (SqInt.continuous_covU h T).measurable.aemeasurable (μ := T.haar)
    rw [integral_map hm i1.aestronglyMeasurable] at i2
    have i3 := (integrable_map_measure i1.aestronglyMeasurable hm).1 i1
    refine ⟨i3.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at i2
    have i4 : ((∫ g, ‖coefOn (ε := P.sgn) σ x y (SqInt.covU h T g)‖ ^ 2 ∂T.haar : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      push_cast
      exact i2
    exact_mod_cast i4
  · exact (hasParam_iff_isDSPar _ P h (σ := σ) fun _ => rfl).2 hσ

theorem of_upq (hE : DiscreteSeriesUpqExists)
    (hM : ∀ p q : ℕ, 1 ≤ p + q → ∀ (T : GrpData p q) (U : URep T), Formalism.MainNotions.SchurIrreducible.IrrU U →
      ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io) :
    DiscreteSeriesCoverExists := by
  intro p q T lam hl
  rcases Nat.eq_zero_or_pos (p + q) with h0 | h0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.1 h0
    exact ⟨Cover.trivZero T, GlobalTheory.SignedParTest.hasParam_zero _ _⟩
  have key : ∀ lam : Ix p q → ℚ, IsParam lam → (∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m) →
      ∃ R : DSRep T, HasParam R lam := by
    intro lam hl hi
    obtain ⟨P, e, -, h, rfl⟩ := exists_blockPar hl hi
    obtain ⟨H, _, _, σ, hσ⟩ := hE _ P.sgn P.lam P.hc
    exact exists_of_isDSPar T (hM p q h0 T) P h hσ
  obtain ⟨P, e, -, h, rfl | rfl⟩ := isParam_cases hl
  · exact key _ hl fun a => ⟨(P.hc.2 (e a)).choose, by simp [blockPar, ratEntry]⟩
  · obtain ⟨R, hR⟩ := key (fun a => blockPar P e a + 1 / 2 + 1 / 2)
      ⟨fun x y e => hl.1 (add_left_injective _ e), fun x y e => by simpa using hl.2.1 x y e,
        fun x => by
          obtain ⟨k, hk⟩ := hl.2.2.1 x
          exact ⟨k + 1, by push_cast; linarith⟩,
        fun x y => by simpa using hl.2.2.2 x y⟩
      fun a => ⟨(P.hc.2 (e a)).choose + 1, by simp only [blockPar, ratEntry]; push_cast; ring⟩
    exact ⟨Cover.twist R, (Cover.hasParam_twist R _).2 hR⟩

end GlobalTheory.Published.CoverSeries

end
end
