module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bundle001
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

open GlobalTheory.CompanionTheory.SW.FibreRatio

theorem isFibreFamily_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) (h : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam 1 M)
      (fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) id
      {X : Fin 1 → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} lam Set.univ
      (fun s => m (hermScal R σ s)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hc1, hc2, hc3⟩ := hm
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have hcq : Continuous (qS R σ (F := F) (E := E)) := continuous_qS R htr
  have hmap : coordHerm R σ b lam 1 = lam.map (hermScal R σ) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hcs.measurable hA, ← coordHerm_qS R h htr b lam (hcs.measurable hA)]
    congr 1
    ext S
    show S ∈ A ↔ hermScal R σ (qS R σ S) ∈ A
    rw [hermScal_qS R h S]
  have hemb : MeasurableEmbedding (hermScal R σ (F := F) (E := E)) :=
    (Homeomorph.mk ⟨hermScal R σ, qS R σ, qS_hermScal R h, hermScal_qS R h⟩ hcs hcq).measurableEmbedding
  refine ⟨fun s => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hc1 (hermScal R σ s))
    rintro X ⟨hX, hXU⟩
    refine ⟨?_, hXU⟩
    have e : gramR R σ J X = ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  · rw [hc2 φ hφ, hmap, hemb.lintegral_map]
  · obtain ⟨ha, hb⟩ := hc3 φ hφc hφs hφU
    exact ⟨fun s _ => ha _ (Set.mem_univ _),
      (hb.comp hcs.continuousOn (fun _ _ => Set.mem_univ _))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact LengthFibre.isFibreFamily_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ b lam hlam.1 m hm

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  · intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

variable {D : D7} {m r s : ℕ}

def joinAdd (D : D7) (m r s : ℕ) : Mx D m r × Mx D m s ≃+ Mx D m (r + s) :=
  { joinEquiv with map_add' := fun a b => colJoin_add a.1 b.1 a.2 b.2 }

theorem joinAdd_apply (z : Mx D m r × Mx D m s) : joinAdd D m r s z = colJoin z.1 z.2 := rfl

theorem continuous_joinAdd : Continuous (joinAdd D m r s) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.castAdd s j)) = fun z => z.1 i j :=
      funext fun z => colJoin_castAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_fst
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.natAdd r j)) = fun z => z.2 i j :=
      funext fun z => colJoin_natAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_snd

theorem continuous_joinAdd_symm : Continuous (joinAdd D m r s).symm := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.castAdd s j)
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.natAdd r j)

theorem joinAdd_mem_iff (z : Mx D m r × Mx D m s) :
    joinAdd D m r s z ∈ ratMx D m (r + s) ↔ z ∈ (ratMx D m r).prod (ratMx D m s) := by
  rw [AddSubgroup.mem_prod]
  constructor
  · rintro h
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 h
    refine ⟨mem_ratMx.2 ⟨colL γ, ?_⟩, mem_ratMx.2 ⟨colR γ, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.castAdd s j)
      rw [joinAdd_apply, colJoin_castAdd] at this
      exact this
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.natAdd r j)
      rw [joinAdd_apply, colJoin_natAdd] at this
      exact this
  · rintro ⟨h1, h2⟩
    obtain ⟨p, hp⟩ := mem_ratMx.1 h1
    obtain ⟨q, hq⟩ := mem_ratMx.1 h2
    exact mem_ratMx.2 ⟨colJoin p q, by rw [rat_colJoin, hp, hq, joinAdd_apply]⟩

theorem isCovolOne_colJoin : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r))
    (μs : Measure (Mx D m s)) (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  intro D m r s μr 𝓕r μs 𝓕s hr hs
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := lattice_Mx D m r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := lattice_Mx D m s
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := lattice_Mx D m (r + s)
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m (r + s)) := ⟨rfl⟩
  obtain ⟨hHr, hFr, h1r⟩ := hr
  obtain ⟨hHs, hFs, h1s⟩ := hs
  haveI := hHr
  haveI := hHs
  let e := joinAdd D m r s
  have he : Continuous e := continuous_joinAdd
  have he' : Continuous e.symm := continuous_joinAdd_symm
  let f : (Mx D m r × Mx D m s) ≃ₜ Mx D m (r + s) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  have hfun : (fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) = e := rfl
  rw [hfun]
  refine ⟨e.isAddHaarMeasure_map _ he he', ?_, ?_⟩
  · let g : ratMx D m (r + s) ≃ (ratMx D m r).prod (ratMx D m s) :=
      { toFun := fun γ => ⟨e.symm γ, (joinAdd_mem_iff _).1 (by
          change e (e.symm γ) ∈ _
          rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (joinAdd_mem_iff _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine (isAddFundamentalDomain_prod hFr hFs).image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable.aemeasurable, ?_⟩
      have : ((μr.prod μs).map e).map e.symm = μr.prod μs := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m r × Mx D m s → Mx D m r × Mx D m s) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective, Measure.prod_prod, h1r, h1s, one_mul]

end GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_fiber {R I J : Type} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (π : I → J) {e : I → R} (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun c : J => ∑ c' with π c' = c, e c') := by
  classical
  have hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') =
      if c = d then ∑ c' with π c' = c, e c' else 0 := by
    intro c d
    rw [Finset.sum_mul_sum]
    split_ifs with hcd
    · subst hcd
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · exact he.idem i
      · intro j _ hji
        exact he.ortho hji.symm
      · intro h; exact absurd hi h
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
      rintro rfl
      exact hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  refine ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩
  · change _ * _ = _
    rw [hmul, if_pos rfl]
  · change _ * _ = _
    rw [hmul, if_neg hcd]
  · rw [Finset.sum_fiberwise]
    exact he.complete

theorem chain_pow {M : Type} [Monoid M] {p : ℕ} {x : ℕ → M} (h : ∀ k, x (k + 1) ^ p = x k)
    (m d : ℕ) : x (m + d) ^ p ^ d = x m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem mul_sub_pow {S : Type} [CommRing S] {a x y : S} (h : a * (x - y) = 0) (q : ℕ) :
    a * (x ^ q - y ^ q) = 0 := by
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x y q
  rw [hd, ← mul_assoc, h, zero_mul]

theorem val_modEq {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (c : ZMod N) :
    c.val ≡ (ZMod.castHom h (ZMod M) c).val [MOD M] := by
  have h0 := map_natCast (ZMod.castHom h (ZMod M)) c.val
  rw [ZMod.natCast_zmod_val] at h0
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact h0.symm

variable {l : ℕ} [Fact l.Prime]

theorem sharp_xi_pow (ε : Eps l) (t : PAlg l) (m d : ℕ) :
    t.sharp (t.s (ε.e (m + d))) ^ l ^ d = t.sharp (t.s (ε.e m)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]

theorem sharp_xi_period (ε : Eps l) (t : PAlg l) (m : ℕ) :
    t.sharp (t.s (ε.e m)) ^ l ^ m = 1 := by
  have := sharp_xi_pow ε t 0 m
  rw [zero_add] at this
  rw [this]
  exact ε.sharp_e t

theorem coi_descend (ε : Eps l) (t : PAlg l) (r : ℕ → t.A) (hr : ∀ m, r (m + 1) ^ l = r m)
    {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A) (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) :
    CompleteOrthogonalIdempotents
        (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
      ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') *
        (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨coi_fiber _ he, fun c => ?_⟩
  rw [(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hπ := (Finset.mem_filter.1 hc').2
  have h1 := mul_sub_pow (hc c') (l ^ d)
  rw [← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow] at h1
  have h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val := by
    have hv := val_modEq (pow_dvd_pow l h) c'
    rw [hπ] at hv
    rw [pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]
    exact congrArg _ hv
  rwa [h2] at h1

end GlobalTheory.CompanionTheory.ContUniv
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Unip

variable {D : D7} {n : ℕ}

theorem halfTr_add' (a c : AE D) : halfTr (a + c) = halfTr a + halfTr c := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add (f := _), mul_add]

theorem halfTr_add_cA (s : AE D) : halfTr s + halfTr (cA D s) = trA s := by
  have hinv : Function.Involutive (cA D) := by
    intro a
    have h := congrArg (fun N => N 0 0)
      (GlobalTheory.MixModel.adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a))
    simpa [GlobalTheory.MixModel.adj] using h
  have hcomm : ∀ r : AF D.host.F, cA D (algebraMap (AF D.host.F) (AE D) r) =
      algebraMap (AF D.host.F) (AE D) r := by
    intro r
    simp [Formalism.L2.Theta.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  let e : AE D ≃ₐ[AF D.host.F] AE D :=
    AlgEquiv.ofBijective { cA D with commutes' := hcomm } hinv.bijective
  have htr : trA (cA D s) = trA s := Algebra.trace_eq_of_algEquiv e s
  simp only [GlobalTheory.StdUnn.halfTr]
  rw [htr, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem inner_add_add (V : HSp D) (z x : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (z + x) (z + x) = GlobalTheory.StdUnn.inner V z z + GlobalTheory.StdUnn.inner V z x + GlobalTheory.StdUnn.inner V x z +
      GlobalTheory.StdUnn.inner V x x := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem adj_inner (V : HSp D) (z x : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V z x) = GlobalTheory.StdUnn.inner V x z := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
    Matrix.mul_assoc]

theorem trace_inner_mul (V : HSp D) (b : Mx D n n) (z x : Mx D V.rank n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b)) = Matrix.trace (b * GlobalTheory.StdUnn.inner V z x) := by
  rw [Matrix.trace_mul_comm b]
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    Matrix.trace (b * GlobalTheory.StdUnn.inner V x z) = cA D (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x)) := by
  rw [← GlobalTheory.MixModel.trace_adj, GlobalTheory.MixModel.adj_mul, GlobalTheory.CompanionTheory.EisCovar.Unip.adj_inner, hb,
    Matrix.trace_mul_comm]

theorem quad_shift (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V (z + x) (z + x))) =
      halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V z z)) + trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b))) +
        halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V x (x ⬝ b))) := by
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.inner_add_add, GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul,
    GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul]
  simp only [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add']
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.trace_swap V hb z x,
    ← GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add_cA (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x))]
  abel

theorem mat_inv_unip {g : G D n} {b : Mx D n n} (hg : mat g = blk4 1 b 0 1) : mat g⁻¹ = blk4 1 (-b) 0 1 := by
  have h1 : GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1 = 1 := by
    rw [hg, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      neg_add_cancel, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  calc GlobalTheory.StdUnn.mat g⁻¹ = GlobalTheory.StdUnn.mat g⁻¹ * (GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1) := by
        rw [h1, Matrix.mul_one]
    _ = GlobalTheory.StdUnn.blk4 1 (-b) 0 1 := by
        rw [← Matrix.mul_assoc, GlobalTheory.CompanionTheory.EisCovar.mat_inv_mul', Matrix.one_mul]

end GlobalTheory.CompanionTheory.EisCovar.Unip

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g b hb hg
  unfold GlobalTheory.CompanionTheory.EisCovar.CovAt
  intro v Φ Ψ hΨ
  have hinv := GlobalTheory.CompanionTheory.EisCovar.Unip.mat_inv_unip hg
  funext z
  rw [hinv, hW.unip g b hg Ψ z, hΨ]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [GlobalTheory.CompanionTheory.EisCovar.x_part_mul_block, GlobalTheory.CompanionTheory.EisCovar.y_part_mul_block]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_neg]
  rw [hW.unip g b hg Φ, GlobalTheory.CompanionTheory.EisCovar.Unip.quad_shift V hb z (xPart v)]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.mul_neg,
    Matrix.trace_add, Matrix.trace_neg, map_add, map_neg]
  ring

end GlobalTheory.CompanionTheory.EisCovar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isArithVar_mpStr (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem dim_of_isArithVar (hD : GlobalTheory.CompanionTheory.MixZ.PtDict) {m : ℕ} {n : Fin (m + 1) → ℕ} {Z : Scheme.{0}} [IsIntegral Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {d : ℕ} (hd : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) d) :
    topologicalKrullDim Z = d := by
  obtain ⟨d', hd'⟩ := (isArithVar_mpStr m n).exists_dim_eq i
  obtain ⟨-, -, h₃, -⟩ := hD m n Z i d' hd'
  have h₄ := h₃ hd.2.2.1
  have e : d' + Fintype.card (Fin (m + 1)) = d + Fintype.card (Fin (m + 1)) := by
    exact_mod_cast h₄.2.2.2.symm.trans hd.2.2.2
  rw [hd', Nat.add_right_cancel e]

end GlobalTheory.CompanionTheory.MPDict
end
end
