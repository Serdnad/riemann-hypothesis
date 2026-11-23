module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem exists_bigCell : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  intro H F E _ _ _ _ _ σ B d W r s hB hW v w hw g hg
  obtain ⟨hinj, -, -, -, -, -, -⟩ := GlobalTheory.T.inertCompletionToAdeles_properties σ hw
  obtain ⟨gmul, gone, ginj, gat, gsurj, gvec⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d ⊕ Fin d)
  obtain ⟨gmul', gone', -, -, -, gvec'⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d)
  obtain ⟨hJ, -, -⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d ⊕ Fin d)
  obtain ⟨-, hdiag, hhalfblk⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d)
  obtain ⟨b, δ, hb, hδ, hint, hdet, hdetinv⟩ := GlobalTheory.T.exists_unimodular_frame_inertPlace σ B W r s hB hW hw
  obtain ⟨cc, cO, h2, calg⟩ := GlobalTheory.T.inertCompletionConjugation_properties σ B hB hw
  have hlat := GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert hw W

  have hvec : ∀ x : Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.InertSph.latAt W v ↔ InLat (w.adicCompletionIntegers E) b x := by
    intro x
    rw [hlat]
    constructor
    · rintro ⟨u, hu, he⟩
      have hxu : x = u := funext fun i => hinj (congrFun he i)
      subst hxu
      exact (hb x).1 hu
    · intro hx
      exact ⟨x, (hb x).2 hx, rfl⟩
  have hvec2 : ∀ x : Fin d ⊕ Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.DblVac.latD W v ↔ InLat2 (w.adicCompletionIntegers E) b x := by
    intro x
    exact and_congr (hvec (x ∘ Sum.inl)) (hvec (x ∘ Sum.inr))
  have hsurj2 : ∀ z ∈ GlobalTheory.DblVac.latD W v, ∃ x : Fin d ⊕ Fin d → w.adicCompletion E,
      z = fun i => iotaW hw (x i) := by
    rintro z ⟨h1, h2⟩
    obtain ⟨x1, -, e1⟩ := (hlat _).1 h1
    obtain ⟨x2, -, e2⟩ := (hlat _).1 h2
    refine ⟨Sum.elim x1 x2, funext fun i => ?_⟩
    rcases i with i | i
    · exact congrFun e1 i
    · exact congrFun e2 i

  have hpres : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x)) →
      ∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
    intro P hP z hz
    obtain ⟨x, rfl⟩ := hsurj2 z hz
    rw [gvec]
    exact (hvec2 _).2 (hP x ((hvec2 x).1 hz))
  have hpres' : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v) →
      ∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x) := by
    intro P hP x hx
    have := hP _ ((hvec2 x).2 hx)
    rw [gvec] at this
    exact (hvec2 _).1 this

  have e1 : incM F (dbl W.J) = dbl (incM F W.J) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e2 : (dbl W.J).map (algebraMap E (w.adicCompletion E)) = dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have hskew : (W.J.map (algebraMap E (w.adicCompletion E)))ᵀ =
      -(W.J.map (algebraMap E (w.adicCompletion E))).map (conjW σ hw) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, calg, hW.skew j i, map_neg, neg_neg]
  have h2ne : (2 : w.adicCompletion E) ≠ 0 := by
    have h := (algebraMap E (w.adicCompletion E)).injective.ne (two_ne_zero : (2 : E) ≠ 0)
    rw [show (2 : w.adicCompletion E) = algebraMap E (w.adicCompletion E) 2 from (map_ofNat _ 2).symm]
    exact h

  obtain ⟨hgat, hglat⟩ := hg
  have hgg : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
  have hgg' : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := Units.inv_mul g.1
  have hginvat : At (evFin F v) (GlobalTheory.DblVac.matD g⁻¹ - 1) := by
    intro u hu
    have e : GlobalTheory.DblVac.matD g⁻¹ - 1 = -(GlobalTheory.DblVac.matD g⁻¹ * (GlobalTheory.DblVac.matD g - 1)) := by
      rw [Matrix.mul_sub, hgg', Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hgat u hu, Matrix.mul_zero, neg_zero]
  obtain ⟨P, hP⟩ := gsurj _ hgat
  obtain ⟨Q, hQ⟩ := gsurj _ hginvat
  have hPQ : P * Q = 1 := ginj (by rw [gmul, hP, hQ, gone]; exact hgg)
  have hU : Pᵀ * dbl (W.J.map (algebraMap E (w.adicCompletion E))) * P.map (conjW σ hw) =
      dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    rw [← e2]
    apply (hJ (dbl W.J) P).1
    rw [hP, e1]
    exact g.2
  have hPlat : ∀ z, InLat2 (w.adicCompletionIntegers E) b z →
      InLat2 (w.adicCompletionIntegers E) b (P *ᵥ z) ∧ InLat2 (w.adicCompletionIntegers E) b (Q *ᵥ z) :=
    fun z hz => ⟨hpres' P (fun y hy => by rw [hP]; exact (hglat y hy).1) z hz,
      hpres' Q (fun y hy => by rw [hQ]; exact (hglat y hy).2) z hz⟩

  obtain ⟨P0, P0', hPP, hP0U, hP0d, hP0lat, N, hN, hNlat⟩ :=
    GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition H (w.adicCompletionIntegers E) (conjW σ hw) cc cO h2 h2ne
      (W.J.map (algebraMap E (w.adicCompletion E))) hskew b δ hδ hint hdet hdetinv P Q hPQ hU hPlat

  let u : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨glueW hw P0, glueW hw P0', by rw [← gmul, hPP, gone], by
      have hPP' : P0' * P0 = 1 := mul_eq_one_comm.mp hPP
      rw [← gmul, hPP', gone]⟩
  have hu : u ∈ UG (cA σ) (dbl (incM F W.J)) := by
    show (glueW hw P0)ᵀ * dbl (incM F W.J) * (glueW hw P0).map (cA σ) = dbl (incM F W.J)
    rw [← e1]
    apply (hJ (dbl W.J) P0).2
    rw [e2]
    exact hP0U
  let p : GlobalTheory.DblVac.UD σ W := ⟨u, hu⟩
  have hp : GlobalTheory.DblVac.matD p = glueW hw P0 := rfl
  have hp' : GlobalTheory.DblVac.matD p⁻¹ = glueW hw P0' := rfl
  have hmul : ∀ a c : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * c) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD c :=
    fun _ _ => rfl
  have hpl : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0 (fun x hx => (hP0lat x hx).1)
  have hpl' : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p⁻¹ *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0' (fun x hx => (hP0lat x hx).2)
  have hpg : GlobalTheory.DblVac.matD (p * g) = glueW hw (P0 * P) := by
    rw [gmul, hP]
    rfl
  refine ⟨p, ⟨?_, fun z hz => ⟨hpl z hz, hpl' z hz⟩⟩, ⟨1, ?_⟩, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hp]
    exact gat P0
  · rw [hp]
    refine (hdiag P0 hP0d).trans ?_
    exact (Matrix.mul_one _).symm
  · rw [hpg]
    exact gat _
  · rw [hmul, ← Matrix.mulVec_mulVec]
    exact hpl _ (hglat z hz).1
  · rw [mul_inv_rev, hmul, ← Matrix.mulVec_mulVec]
    exact (hglat _ (hpl' z hz)).2
  ·
    refine ⟨glueW hw N, ?_, ?_⟩
    · have hd : GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = glueW hw ((2 : w.adicCompletion E)⁻¹ •
          ((P0 * P).toBlocks₁₁ + (P0 * P).toBlocks₁₂ + (P0 * P).toBlocks₂₁ + (P0 * P).toBlocks₂₂)) := by
        unfold GlobalTheory.DblVac.diagonalBlockOfMatrix
        rw [hpg]
        exact hhalfblk _
      rw [hd, ← gmul', hN, gone']
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (hlat z).1 hz
      rw [gvec']
      exact (hvec _).2 (hNlat x ((hb x).1 hx))

end GlobalTheory.InertBigCell
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

theorem nsmul_mem_of_mem_halfCoset {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {r x : Mx D m n}
    (hr : K • r ∈ Λ) (h : x ∈ halfCoset e Λ K r) : K • x ∈ Λ := by
  obtain ⟨u, hu, -, rfl⟩ := h
  rw [nsmul_add]
  exact add_mem hr (nsmul_mem (nsmul_mem hu K) K)

theorem eq_of_mem_halfCoset_reps {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {R : Finset (Mx D m n)}
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') {r r₀ x : Mx D m n} (hr : r ∈ R) (hr₀ : r₀ ∈ R)
    (hm : x ∈ halfCoset e Λ K r) (hm₀ : x ∈ halfCoset e Λ K r₀) : r = r₀ := by
  refine hR3 r hr r₀ hr₀ ?_
  rw [← halfCoset_eq hm, halfCoset_eq hm₀]
  exact mem_halfCoset_self _ _ _ _

theorem exists_cosetExpansion_of_depthOK : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  classical
  intro D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep
  by_cases hτ : τ = 0
  · subst hτ
    exact ⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩
  obtain ⟨d₀, hd₀⟩ := Finsupp.support_nonempty_iff.2 hτ
  have hP0 := hexp.1 d₀ hd₀
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  let dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) →
      (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t :=
    fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))
  set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'
  have hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ' := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := hP0.1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := hP0.2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    change Finsupp.sum τ' g = _
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) =
        (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) := fun ρ hρ j =>
      congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1
        ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)
    have hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ' hρ' i =>
      congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1
        ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)
    simp only [g, dat]
    have hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2,
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)) *
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ hρ ρ' hρ' => by
      rw [Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]
    rw [Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']
    show _ = flatProd S t Φ β x y
    by_cases hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)
    · have h1 := fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)
      have h2 := fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)
      choose ρ0 hρ0 hxρ0 using h1
      choose ρ0' hρ0' hyρ0' using h2
      have hmem : ρ0 ∈ Fintype.piFinset R1 := Fintype.mem_piFinset.2 hρ0
      have hmem' : ρ0' ∈ Fintype.piFinset R2 := Fintype.mem_piFinset.2 hρ0'
      have hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 →
          ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ) := by
        intro ρ hρ hne
        obtain ⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)
        exact eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)
      have hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' →
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ) := by
        intro ρ' hρ' hne
        obtain ⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)
        exact eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)
      rw [Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]
      case s1 =>
        intro ρ hρ hne
        exact Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _
      case s2 =>
        intro ρ' hρ' hne
        exact mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)
      refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_))
        (Finset.prod_eq_one fun i _ => ?_)).trans ?_
      · exact Set.indicator_of_mem (hxρ0 j) _
      · exact Set.indicator_of_mem (hyρ0' i) _
      rw [mul_one, mul_one]
      choose u hu hu' hxu using hxρ0
      choose v hv hv' hyv using hyρ0'
      have hx' : x = ρ0 + K • u := funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j
      have hy' : y = ρ0' + K • v := funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i
      rw [hx', hy']
      exact (hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1)
        (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm
    · have hzero : flatProd S t Φ β x y = 0 := by
        by_contra h
        exact hin (hdep.1 x y hx hy h)
      rw [hzero]
      refine Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_
      rw [Fintype.mem_piFinset] at hρ hρ'
      rcases not_and_or.1 hin with h | h
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem
          (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem
          (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))
  · obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2

end GlobalTheory.DepthUnf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem nsmul_mem_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {x : WO (G.pS p) (G.pT p)} (hx : d.fn x ≠ 0) : k • x ∈ pairLat G p := by
  obtain ⟨x₀, -, h1, hfn⟩ := h
  rw [hfn] at hx
  obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
  rw [nsmul_add]
  exact add_mem h1 (nsmul_mem (nsmul_mem hu k) k)

theorem fn_add_nsmul_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ pairLat G p) (hu' : IsHalf d.e u) (x : WO (G.pS p) (G.pT p)) :
    d.fn (x + k • u) = d.fn x := by
  obtain ⟨x₀, -, -, hfn⟩ := h
  rw [hfn]
  by_cases hx : x ∈ halfCoset d.e (pairLat G p) k x₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]

theorem depthOK_of_isCosetExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  intro D T L sc G W U S t Φ β k τ h
  obtain ⟨-, ⟨e, he, hP, hsum⟩, hcos⟩ := h
  refine ⟨e, he, ⟨hP, hsum⟩, ?_, ?_⟩
  · intro x y hx hy hne
    unfold flatProd at hne
    rw [← hsum x y hx hy] at hne
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    beta_reduce at hne
    have h1 : ∏ j, (d.1 j).fn (x j) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, zero_mul])
    have h2 : ∏ i, (d.2 i).fn (y i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => nsmul_mem_of_isCosetDatum ((hcos d hd).1 j) (h1 j (Finset.mem_univ _)),
      fun i => nsmul_mem_of_isCosetDatum ((hcos d hd).2 i) (h2 i (Finset.mem_univ _))⟩
  · intro x u y v hx hy hu hv
    have hx' : ∀ j, IsHalf e ((x + k • u) j) := fun j a b => by
      show e * (x j + k • u j) a b = (x j + k • u j) a b
      rw [Matrix.add_apply, mul_add, hx j a b, isHalf_nsmul_of k (hu j).1 a b]
    have hy' : ∀ i, IsHalf e ((y + k • v) i) := fun i a b => by
      show e * (y i + k • v i) a b = (y i + k • v i) a b
      rw [Matrix.add_apply, mul_add, hy i a b, isHalf_nsmul_of k (hv i).1 a b]
    unfold flatProd
    rw [← hsum _ _ hx' hy', ← hsum x y hx hy]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hx1 : ∀ j, (d.1 j).fn ((x + k • u) j) = (d.1 j).fn (x j) := fun j =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).1 j) (hu j).2 (((hP d hd).1 j).2.1 ▸ (hu j).1) (x j)
    have hy1 : ∀ i, (d.2 i).fn ((y + k • v) i) = (d.2 i).fn (y i) := fun i =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).2 i) (hv i).2 (((hP d hd).2 i).2.1 ▸ (hv i).1) (y i)
    simp only [hx1, hy1]

end GlobalTheory.DepthUnf

end
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.adelicVacuum_standardLattices_readsTheta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  first | exact @GlobalTheory.VacRead.vacuum_reads_theta | exact GlobalTheory.VacRead.vacuum_reads_theta | (intros; apply GlobalTheory.VacRead.vacuum_reads_theta <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  first | exact @GlobalTheory.logDet_local_eq_unit_mul_prod | exact GlobalTheory.logDet_local_eq_unit_mul_prod | (intros; apply GlobalTheory.logDet_local_eq_unit_mul_prod <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.vertical_tangentFrame_jacobian_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  first | exact @GlobalTheory.LogPole.vert_jac_det_one | exact GlobalTheory.LogPole.vert_jac_det_one | (intros; apply GlobalTheory.LogPole.vert_jac_det_one <;> assumption)
end
