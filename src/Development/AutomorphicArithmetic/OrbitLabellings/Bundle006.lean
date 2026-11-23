module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Formalism.LocalToGlobal.CharacterGerms.Bundle029
public import Development.AutomorphicArithmetic.OrbitLabellings.RowLab
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Formalism.LocalToGlobal.CharacterGerms.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.Bundle005

@[expose] public section

section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth UpperTheory.G2 NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.exists_orbit_labelling_at_inert_prime_of_odd_order :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv)
    (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl →
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    V.l = resCharOf la → V.l ≠ 2 → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) →
    N.cls V.l = PrimeClass.inertClass → Odd (N.ordP V.l) → ∀ (j : ℕ) (Z : Finset (RPl N.R)), RF.IsReps (parOf N j V.l) Z → ∀ n j₁ j₂ : ℕ,
    ∃ lab : Formalism.L2.FormalSeriesBounds.LabS E C {z // z ∈ Z} (2 * N.ordP V.l), LabSArith V io ι lab ∧
      lab.hd = (N.ordP V.l : ZMod (2 * N.ordP V.l)) ∧ lab.n = n ∧ lab.j = j₁ ∧ lab.j' = j₂ ∧
      (∀ o g s, lab.big o g s ↔ (Even s.val ↔ g = 0)) ∧
      (∀ o s, lab.tau o s = if Even s.val then pl (N.pos V.l o.1 s.val) else ComplexEmbedding.conjugate (pl (N.pos V.l o.1 s.val))) ∧
      Function.Surjective (fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => lab.tau x.1 x.2) ∧ ¬ (V.l : ℤ) ∣ NumberField.discr E := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ _ V ι hι hc hl h2 hla hC ho j Z hZ n j₁ j₂
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E := by
    have h := hC
    unfold NumDatum.cls primeClass at h
    refine hP.unr _ V.l_prime (fun h2 => ?_) (fun hq => ?_) (fun hd => ?_)
    · rw [if_pos h2] at h
      cases h
    · rw [if_pos hq] at h
      split_ifs at h
    · rw [if_pos hd] at h
      split_ifs at h
  have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
      emA3 io ι (pl w) x ^ V.l) := by
    intro w x
    obtain ⟨y, hy, e⟩ := hP.frob la (Or.inl (hl ▸ hC)) w x
    have := hla y hy
    rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
    exact this
  obtain ⟨lab, h1, h3, h4, h5, h6, h7, h8, h9⟩ :=
    UpperTheory.G2.RowLab.exists_lab c N pl hP.inj hP.psi T io C V ι hι hc h2 hunr hf ho Z hZ n j₁ j₂
  exact ⟨lab, h1, h3, h4, h5, h6, h7, h8, h9, hunr⟩
end

section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private theorem UpperTheory.extend_sigma_coefficients_by_zero {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem UpperTheory.labelSetGeo_of_labelSetArith :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    LabSGeo C3 ι Y lab := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ d _ lab ha
  have hsep1 : ∀ o (s s' : ZMod d), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => ha.sep (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod d) (lab.tau o) (hsep1 o)
  refine { em_int := fun _ _ x => embedding_integral ι _ x
           em_conj := ?_
           e_int := fun _ _ i => a3uvec_int C3 hι _ i
           e_eig := fun o x a => (hgeo o).2.1 x.1 x.2 a
           e_sat := ?_
           e_full := ?_ }
  · intro o a x
    rw [← ha.conj o a]
    exact (embedding_conjugate hstar ι _ x).symm
  · intro o
    obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
    exact ⟨w, h1, fun q q' => (h2 q q').trans (by congr)⟩
  · intro o a v hv
    obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
    obtain ⟨b', h1, h2⟩ := UpperTheory.extend_sigma_coefficients_by_zero (fun s => Dw.mult (lab.tau o s)) (selfLieBasisVector C3 ι lab o) a b
    exact ⟨b', h1, hb.trans h2⟩
end
