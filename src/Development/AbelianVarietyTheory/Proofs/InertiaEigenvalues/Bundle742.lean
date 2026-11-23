module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle413
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle031
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle733
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LargeO

def sysPol (n : ℕ) {E : Type} [Field E] [NumberField E] (c : HeightOneSpectrum (𝓞 E) → ℕ → ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((normV v : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c v k) * X ^ (n - k)

def BigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (Sf : Finset ℂ) : Prop :=
  ∀ c ∈ Es, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ Sf, ι.symm z ∈ K) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar l),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l))) → IsSSRep ρ →
      (∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
          IsFrob (F := D.host.E) B (normV v) σ →
          ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)).charpoly.map ι.toRingHom = sysPol D.R.nV c v) →
      ∃ Pm : GL (Fin D.R.nV) (Qbar l), ∀ g s t,
        ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)) s t ∈ K

theorem bigOk_mono {D : D7} {l : ℕ} [Fact l.Prime] {Q : Finset (PlE D.host)} {Es : Set (PlE D.host → ℕ → ℂ)}
    {ι : Qbar l ≃+* ℂ} {Sf Sf' : Finset ℂ} (h : BigOk D l Q Es ι Sf) (hs : Sf ⊆ Sf') : BigOk D l Q Es ι Sf' :=
  fun c hc K hK => h c hc K fun z hz => hK z (hs hz)

theorem bigOk_cast {D : D7} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (e : p = q) {Q : Finset (PlE D.host)}
    {Es : Set (PlE D.host → ℕ → ℂ)} {ι : Qbar p ≃+* ℂ} {Sf : Finset ℂ} (h : BigOk D p Q Es ι Sf) :
    BigOk D q Q Es (qCast e ι) Sf := by
  subst e; exact h

theorem exists_bigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (hE : Es.Finite) (hch : GlobalTheory.RowTie.ChebSplit D.nd) : ∃ Sf, BigOk D l Q Es ι Sf := by
  classical
  let Good : PlE D.host → Prop := fun v =>
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q
  let U : Set (G D.host.E D.nd.Om) := {σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}
  have hU : Dense U := GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch
  let p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun c σ =>
    if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0
  have hS := fun c => GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys l ι D.host.E D.nd.Om D.R.nV U (p c) hU
  choose Sc hSc using hS
  refine ⟨hE.toFinset.biUnion Sc, ?_⟩
  intro c hc K hK ρ hcont hss hchar
  refine hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_
  intro σ hσ
  simp only [p, dif_pos hσ]
  obtain ⟨hg, B, hB, hF⟩ := Classical.choose_spec hσ
  exact hchar _ hg B σ hB hF

theorem charpoly_pt : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.nd.l i) ∧
      v ∉ placesS D (D.nd.l i) ∧ v ∉ D.nd.Q i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
        sysPol D.R.nV (ptSys D i x) v := by
  intro D i x ρ hρ v hv B σ hB hF
  have hso : SplitOut D.nd i v := ⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩
  rw [hρ.2.2 v hso B σ hB hF, Polynomial.map_map]
  have hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i := rfl
  rw [hcomp]
  unfold heckePol sysPol

  rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hg : GenAt D (D.nd.l i) (D.nd.Q i) v k := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩
  simp only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul,
    map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

theorem model_of_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (P : GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ →
    (∀ g s t, ∃ x, A.iotaQ i x = ((P⁻¹ * ρ g * P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) →
    ∃ (r : G H.E N.Om →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ P hc hP
  let ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)) := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P := fun g => by
    simp [ρ', MulAut.conj_apply]
  have hc' : SumRepresentations.At.ContQ N i ρ' := by
    unfold SumRepresentations.At.ContQ at hc ⊢
    have e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) =
        fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) := by
      funext g; rw [hρ']; rfl
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, Pm, hr⟩ := GlobalTheory.T.exists_integral_model_rep_coeffRing N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)
  refine ⟨r, P * Pm, fun g => ?_⟩
  rw [hr g, hρ', mul_inv_rev]
  group

end GlobalTheory.LargeO
end
end

section

noncomputable section

namespace GlobalTheory.PendOf.LabIneAll

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open Polynomial GlobalTheory.Pass GlobalTheory.PendOf GlobalTheory.WeilDeligne

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem teich_zero {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

end Alg

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω}

theorem mem_of_isOpen {H : Subgroup (Ine (F := E) A)} (hH : IsOpen (H : Set (Ine (F := E) A)))
    {γ : G E Ω} (hγ : TameGenAt A γ) (h1 : (⟨γ, hγ.1⟩ : Ine (F := E) A) ∈ H)
    (hw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A → σ ∈ H) (σ : Ine (F := E) A) : σ ∈ H := by
  have hK : IsClosed ((H.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (H.isClosed_of_isOpen hH)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ H.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, hw _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem isOfFinOrder_of_isOpen {M : Type} [Group M] (φ : Ine (F := E) A →* M)
    (hφ : IsOpen (φ.ker : Set (Ine (F := E) A))) (σ : Ine (F := E) A) : IsOfFinOrder (φ σ) := by
  have : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have : Finite (Ine (F := E) A ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hφ
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨φ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rw [← map_pow]
  exact φ.ker.pow_index_mem σ


open Classical in
theorem charpoly_eq_of_gen {n : ℕ} (ρ : Ine (F := E) A →* GL (Fin n) ℂ)
    (hρ : ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ U → ρ σ = 1)
    {ι : Type} (s : Multiset ι) (χ : ι → G E Ω → ℂ)
    (h1 : ∀ x ∈ s, χ x 1 = 1)
    (hmul : ∀ x ∈ s, ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, χ x (σ * σ') = χ x σ * χ x σ')
    (hwild : ∀ x ∈ s, ∀ σ ∈ Wild E A, χ x σ = 1)
    (hopen : ∀ x ∈ s, ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ ∈ U, σ ∈ Ine (F := E) A → χ x σ = 1)
    {γ : G E Ω} (hγ : TameGenAt A γ)
    (hρw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A →
      ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (X - 1) ^ n)
    (hργ : ((ρ ⟨γ, hγ.1⟩ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly =
      (s.map fun x => X - C (χ x γ)).prod)
    (σ : Ine (F := E) A) :
    ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun x => X - C (χ x σ)).prod := by
  let T := s.toFinset
  let c : T → (Ine (F := E) A →* ℂˣ) := fun x => MonoidHom.toHomUnits
    { toFun := fun σ => χ x (σ : G E Ω)
      map_one' := h1 x (Multiset.mem_toFinset.1 x.2)
      map_mul' := fun σ σ' => hmul x (Multiset.mem_toFinset.1 x.2) σ σ.2 σ' σ'.2 }
  have hc : ∀ x σ, ((c x σ : ℂˣ) : ℂ) = χ x (σ : G E Ω) := fun _ _ => rfl
  let Φ : Ine (F := E) A →* GL (Fin n) ℂ × (T → ℂˣ) := ρ.prod (Pi.monoidHom c)
  obtain ⟨U, hU, hUρ⟩ := hρ
  choose V hV hVχ using fun x : T => hopen x (Multiset.mem_toFinset.1 x.2)
  let W : Set (Ine (F := E) A) := Subtype.val ⁻¹' ((U : Set (G E Ω)) ∩ ⋂ x, (V x : Set (G E Ω)))
  have hWo : IsOpen W := continuous_subtype_val.isOpen_preimage _ (hU.inter (isOpen_iInter_of_finite hV))
  have hWk : ∀ σ ∈ W, Φ σ = 1 := by
    intro σ hσ
    refine Prod.ext (hUρ σ hσ.1) (funext fun x => Units.ext ?_)
    show χ x (σ : G E Ω) = 1
    exact hVχ x σ (Set.mem_iInter.1 hσ.2 x) σ.2
  have h1W : (1 : Ine (F := E) A) ∈ W := ⟨U.one_mem, Set.mem_iInter.2 fun x => (V x).one_mem⟩
  have hker : IsOpen (Φ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (hWo.mem_nhds h1W) fun σ hσ => MonoidHom.mem_ker.2 (hWk σ hσ))
  have hkerρ : IsOpen (ρ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => MonoidHom.mem_ker.2 (congrArg Prod.fst (MonoidHom.mem_ker.1 hσ)))
      hker
  let γ' : Ine (F := E) A := ⟨γ, hγ.1⟩
  let H := (Subgroup.zpowers (Φ γ')).comap Φ
  have hH : IsOpen (H : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => Subgroup.mem_comap.2 (by
      rw [MonoidHom.mem_ker.1 hσ]; exact one_mem _)) hker
  have hσH : σ ∈ H := by
    refine mem_of_isOpen hH hγ (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)) (fun τ hτ => ?_) σ
    refine Subgroup.mem_comap.2 ?_
    have hρ1 : ρ τ = 1 := by
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_isOpen ρ hkerρ τ)
      exact Units.ext (GlobalTheory.FinOrd.eq_one_of_pow_eq_one_of_charpoly ℂ n _
        ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]⟩ (hρw τ hτ))
    have hΦ1 : Φ τ = 1 := by
      refine Prod.ext hρ1 (funext fun x => Units.ext ?_)
      show χ x (τ : G E Ω) = 1
      exact hwild x (Multiset.mem_toFinset.1 x.2) τ hτ
    rw [hΦ1]
    exact one_mem _
  obtain ⟨m, hm⟩ := ((isOfFinOrder_of_isOpen Φ hker γ').mem_powers_iff_mem_zpowers).2 (Subgroup.mem_comap.1 hσH)
  have hρm : ρ σ = ρ γ' ^ m := by
    have := congrArg Prod.fst hm
    simpa [Φ] using this.symm
  have hχm : ∀ x ∈ s, χ x γ ^ m = χ x σ := by
    intro x hx
    have := congrArg (fun p : GL (Fin n) ℂ × (T → ℂˣ) => ((p.2 ⟨x, Multiset.mem_toFinset.2 hx⟩ : ℂˣ) : ℂ)) hm
    simp only [Φ, MonoidHom.prod_apply, Prod.pow_snd, Pi.pow_apply, Units.val_pow_eq_pow_val,
      Pi.monoidHom_apply] at this
    exact this
  rw [hρm, Units.val_pow_eq_pow_val, charpoly_pow_of_prod _ s (fun x => χ x γ) hργ m]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => by rw [hχm x hx])

end Local

theorem main : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  intro D hR hD hG
  obtain ⟨γ, hγ, hlab⟩ := hG
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.PendOf.Model.exists_tameOm D γ hγ
  refine ⟨Ω, fun k w hw L hL => ?_⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  obtain ⟨ρ, hρ, hρP⟩ := hR k w hw L
  have hT : TameLP D L := ((hD k w hw L).2).1 hL
  have hγw := hγ.2 k w hw
  have hlabγ := hlab k w hw L hL
  have hs0 : ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L), x ≠ 0 := by
    intro x hx h0
    subst h0
    have hdvd : X ∣ ((ρ ⟨γ k w, hγw.1⟩ : GL (Fin (D.naut.lpDim L)) ℂ) :
        Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly := by
      rw [← hρP ⟨γ k w, hγw.1⟩]
      rw [show ((⟨γ k w, hγw.1⟩ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = γ k w from rfl, hlabγ]
      have := Multiset.dvd_prod (Multiset.mem_map_of_mem (fun x => X - C (D.ntypes.teichC k x)) hx)
      simpa [teich_zero (D.ntypes.teichC k) (D.ntypes.teichC_inj k)] using this
    rw [X_dvd_iff] at hdvd
    have hdet := Matrix.isUnits_det_units (ρ ⟨γ k w, hγw.1⟩)
    rw [Matrix.det_eq_sign_charpoly_coeff, hdvd, mul_zero] at hdet
    exact not_isUnit_zero hdet
  refine (hρP ⟨σ, hσ⟩).trans (charpoly_eq_of_gen ρ hρ _ (fun x τ => Ω.om k w x τ)
    (fun x hx => Ω.om_one k w x (hs0 x hx))
    (fun x hx => Ω.om_mul k w x (hs0 x hx))
    (fun x hx τ hτ => Ω.om_wild k w hw x (hs0 x hx) τ hτ)
    (fun x hx => Ω.om_open k w x (hs0 x hx)) hγw
    (fun τ hτ => (hρP τ).symm.trans (hT τ τ.2 hτ)) ?_ ⟨σ, hσ⟩)
  rw [← hρP ⟨γ k w, hγw.1⟩]
  refine hlabγ.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_))
  rw [hΩ k w hw x (hs0 x hx)]

end GlobalTheory.PendOf.LabIneAll
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.TwoBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem addVal_le_of_notMem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l x : O}
    (hx : x ∉ Ideal.span {l} * IsLocalRing.maximalIdeal O) :
    IsDiscreteValuationRing.addVal O x ≤ IsDiscreteValuationRing.addVal O l := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hlt.le
  by_cases hy : IsUnit y
  · rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hy, add_zero] at hlt
    exact lt_irrefl _ hlt
  · exact hx (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self l) hy)

noncomputable def bound (w e r k : ℕ) : ℕ := Nat.rec w (fun _ b => 2 * (e + 1) * b + 2 + 2 * r) k

theorem bound_succ (w e r k : ℕ) : bound w e r (k + 1) = 2 * (e + 1) * bound w e r k + 2 + 2 * r := rfl

theorem bound_step (w e r k : ℕ) : bound w e r k + 1 + 2 * r ≤ bound w e r (k + 1) := by
  rw [bound_succ]; nlinarith [Nat.zero_le (e * bound w e r k)]

theorem bound_mono (w e r : ℕ) : Monotone (bound w e r) :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (bound_step w e r k)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}

theorem NF_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NF bkP i s M d P c) :
    NF bkP i s M d P c' := fun Q hQ a Φ hΦ F hF =>
  (h Q hQ a Φ hΦ F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩

theorem NFit_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NFit bkP i s M d P c) :
    NFit bkP i s M d P c' := fun Q hQ a Φ hΦ =>
  (h Q hQ a Φ hΦ).imp id fun ⟨b, b', hb⟩ => ⟨b, b', fun F hF => (hb F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩⟩

theorem induct (hl : 0 < nu X i) {t R₀ : ℕ} (f : Fin t → X.Sig i) (hG : ∀ j, Grow bkP i (f j)) (hS : ∀ j, Step bkP i (f j))
    {H : Subgroup (GE N)} {S A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {w e : ℕ}
    (he : IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e)
    (hM : bound w e D.R.r t ≤ X.l i ^ (M - nu X i - 1)) (h3 : nu X i + 2 ≤ M)
    (hd : AdmFam X i M H S d) (hLH : L ≤ H) (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : ∀ j, Small2 i (f j) M L z)
    (P₀ : Fin (R₀ + t) ⊕ Fin R₀ → PlE D.host) (h₀ : PiLocalization₂ i M d A L z P₀) (hF : ∀ j, NFit bkP i (f j) M d P₀ (w + 1)) :
    ∀ k, k ≤ t → ∃ P : Fin (R₀ + t) ⊕ Fin (R₀ + k) → PlE D.host, (∀ a, P (.inl a) = P₀ (.inl a)) ∧ PiLocalization₂ i M d A L z P ∧
      (∀ j, NFit bkP i (f j) M d P (bound w e D.R.r k + 1)) ∧
      ∀ j : Fin t, j.val < k → NF bkP i (f j) M d P (bound w e D.R.r k + 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨P₀, fun _ => rfl, h₀, hF, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hP, hSt, hFit, hNF⟩ := ih (by omega)
    have hb : bound w e D.R.r (k + 1) ≤ X.l i ^ (M - nu X i - 1) := (bound_mono w e D.R.r hk).trans hM
    have hs := bound_step w e D.R.r k
    obtain ⟨P', hE, hSt', hN⟩ := hS ⟨k, hk⟩ hl M (R₀ + t) (R₀ + k) H S d A L z P (bound w e D.R.r k) e (by omega) he hb h3
      hd hLH hz (hL _) hSt (hFit _)
    have hg := fun j => hG j hl M (R₀ + t) (R₀ + k) d A L z P P' (bound w e D.R.r k + 1) (by omega) (hs.trans hb) h3 hz
      (hL j) hSt' hE
    refine ⟨P', fun a => (hE (.inl a)).trans (hP a), hSt', fun j => NFit_mono (by omega) ((hg j).2 (hFit j)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact NF_mono (by omega) ((hg j).1 (hNF j hj))
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact NF_mono (Nat.le_succ _) hN

theorem thmC_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → Start bkP i s ∧ Grow bkP i s ∧ Step bkP i s) → ThmC bkP := by
  intro D N X bkP hAB hCh hP i hl T hT
  obtain ⟨R₀, hR⟩ := hCh i T hT
  have : Finite (X.Sig i) := (X.finSig i).finite
  obtain ⟨t, f, -, hf⟩ := (Set.toFinite T).fin_param
  have hfT : ∀ j, f j ∈ T := fun j => hf ▸ Set.mem_range_self j
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hl0 : (X.l i : X.O0 i) ≠ 0 := fun h0 => by
    have h1 : (X.emb0 i) (X.l i : D.LL0) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (X.O0 i) (FractionRing (X.O0 i))), h0, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 ((map_eq_zero _).1 h1))
  obtain ⟨e, he⟩ : ∃ e : ℕ, IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e := by
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (pow_ne_zero (nu X i) hl0))
    exact ⟨e, he.symm⟩
  refine ⟨R₀ + t, bound (4 * D.R.r * R₀) e D.R.r t, bound (4 * D.R.r * R₀) e D.R.r t + nu X i + 3,
    fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hw : 4 * D.R.r * R₀ ≤ bound (4 * D.R.r * R₀) e D.R.r t := bound_mono (4 * D.R.r * R₀) e D.R.r (Nat.zero_le t)
  have hlt : 4 * D.R.r * R₀ + 2 < X.l i ^ M := lt_of_le_of_lt (by omega) (Nat.lt_pow_self (n := M) hp.one_lt)
  have hle : bound (4 * D.R.r * R₀) e D.R.r t ≤ X.l i ^ (M - nu X i - 1) :=
    le_trans (by omega) (Nat.lt_pow_self (n := M - nu X i - 1) hp.one_lt).le
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, hLi⟩ := GlobalTheory.ResSel.SmallSub.exists_small D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  have hh' : ∀ a, Fin.append h (fun _ : Fin t => (1 : GE N)) a ∈ L := fun a => by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left]; exact hh a
    · rw [Fin.append_right]; exact L.one_mem
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A (R₀ + t)
    (Fin.append h fun _ => 1) (fun a => ⟨hLH (hh' a), hLζ _ (hh' a)⟩)
  choose φ g hφ hg using hFr
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh' a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hinj : Function.Injective (Sum.map id (Fin.castAdd t) : Fin (R₀ + t) ⊕ Fin R₀ → Fin (R₀ + t) ⊕ Fin (R₀ + t)) :=
    Function.injective_id.sumMap (Fin.castAdd_injective _ _)
  have h₀ : PiLocalization₂ i M d A L z (fun q : Fin (R₀ + t) ⊕ Fin R₀ => P (Sum.map id (Fin.castAdd t) q)) := by
    refine ⟨⟨fun q => hAux.1 _, fun q q' hq => hinj (hAux.2.1 _ _ hq), fun q => hAux.2.2 _⟩,
      fun a => ⟨fun v hv B hB => (hIne _ v hv B hB).trans hUL', fun σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hUL' hg⟩,
      fun a => ⟨dec_le_of_frob_mem (N.plOm.2 _) (hφ (Fin.castAdd t a)) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL _), fun b σ hσ => ?_⟩⟩
    have := hSt.2 (Fin.castAdd t a) b σ hσ
    simpa [Fin.ext_iff] using this
  have hc := hco (fun a => φ (Fin.castAdd t a)) (fun a => GlobalTheory.TwistDet.cConj X (φ (Fin.castAdd t a)))
    (fun a => ⟨hcj _, g (Fin.castAdd t a), by simpa using (hg (Fin.castAdd t a)).1⟩)
  rw [if_neg hl.ne'] at hc
  obtain ⟨P', hP', hSt', -, hNF⟩ := induct hl f (fun j => (hP i _ (hT _ (hfT j))).2.1) (fun j => (hP i _ (hT _ (hfT j))).2.2)
    he hle (by omega) hd hLH hz (fun j => ⟨hLs _ (hfT j), hLζ, hLi _ (hfT j)⟩) _ h₀
    (fun j => (hP i _ (hT _ (hfT j))).1 M (R₀ + t) R₀ d A L z _ _ _ (Nat.le_add_right _ _) hlt hz (hLs _ (hfT j)) h₀
      (fun a => ⟨hφ _, hcj _⟩) (hc _ (hfT j))) t le_rfl
  refine ⟨P', hSt'.1, ⟨fun a σ hσ => ?_, fun a b σ hσ => ?_⟩, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  · rw [hP' a] at hσ
    exact (hSt.1 a σ hσ).imp fun _ hg => hg.2
  · simpa [Fin.ext_iff] using (hSt'.2.2 a).2 b σ hσ
  · obtain ⟨j, rfl⟩ : s ∈ Set.range f := hf ▸ hs
    obtain ⟨m, hm, hu⟩ := hNF j j.2 Q hQ a Φ hΦ F hF
    exact ⟨m, Nat.lt_succ_iff.1 hm, addVal_le_of_notMem hu⟩

end GlobalTheory.StepTwo.TwoBound
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conjugate_definiteForms_descend_numberField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  first | exact @GlobalTheory.ConjDesc.conj_desc | exact GlobalTheory.ConjDesc.conj_desc | (intros; apply GlobalTheory.ConjDesc.conj_desc <;> assumption)
end
