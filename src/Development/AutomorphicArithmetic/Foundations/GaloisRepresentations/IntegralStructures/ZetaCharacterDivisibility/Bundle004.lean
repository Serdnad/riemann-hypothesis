module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
end

section

open Polynomial

namespace UpperTheory.Gal.Int.Div

theorem sepPin_of : SepPin := by
  intro k _ a M Q hQm hQd hQ hsep
  have key : M.charpoly ∣ Q := by
    rw [← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]
    rw [← M.charpoly_map]
    have hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0 := by
      have e : M.map (algebraMap k (AlgebraicClosure k)) =
          (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M := rfl
      rw [e, Polynomial.aeval_algHom_apply, hQ, map_zero]
    have hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0 := by
      have e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) =
          Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k))) := rfl
      rw [e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply,
        Polynomial.aeval_map_algebraMap, hQ', map_zero]
    have hmon := (M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))
    rw [(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]
    apply Multiset.prod_dvd_prod_of_le
    apply Multiset.map_le_map
    have hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup := by
      rw [M.charpoly_map]
      exact nodup_roots hsep.map
    rw [Multiset.le_iff_subset hnd]
    intro μ hμ
    have hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ :=
      (mem_roots hmon.ne_zero).mp hμ
    rw [← Matrix.charpoly_toLin'] at hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv
    rw [Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply] at hv'
    have h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0 :=
      (smul_eq_zero.mp hv'.symm).resolve_right hv.2
    rw [mem_roots (Polynomial.map_monic_ne_zero hQm)]
    exact h0
  exact (eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key
    (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm

end UpperTheory.Gal.Int.Div
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divDet_of :
    DenseUs → DetFrob → DivDet := by
  intro hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g
  obtain ⟨hrc, -, V, X, hVo, hVd, hV⟩ := hr
  have hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det :=
    Continuous.matrix_det (Units.continuous_val.comp hrc)
  have hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp hψ.1
  have hdense := ((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage
    (Homeomorph.inv (G E Ω)).isOpenMap
  refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g
  rintro x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩
  have hx : (x⁻¹)⁻¹ = x := inv_inv x
  have hch := (hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV
  rw [hx] at hch
  have hψv := (hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr
  rw [hx] at hψv
  apply ι.injective
  rw [hψv]
  have hcard : (algSat a (normV w) B).card = a := by
    have h1 := congrArg Polynomial.natDegree hch
    rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hch
  simp only [Polynomial.coeff_map] at h0
  have hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det =
      (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0 := by
    simpa using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))
  have h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) =
      (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 := h0
  have h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 =
      (-1) ^ a * (algSat a (normV w) B).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    have : (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) =
        Multiset.map Neg.neg (algSat a (normV w) B) :=
      Multiset.map_congr rfl fun b _ => by simp
    rw [this, Multiset.prod_map_neg, hcard]
  show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _
  rw [hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpSeed_of :
    CoverIn → SSBlock → SubLoc → LocConj → JumpCard → JumpCondition := by
  intro h1 h2 h3 h4 h5 E Ω _ _ _ _ _ _ l _ ι a dd U r ρ hss hcov w hcrys hocc P AI hT A hA O _ _ _ Bw hj
  have hc := hcrys P AI hT A hA O Bw hj
  have hdr := ((h4 l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)).1 hc).1
  refine ⟨hc, hdr, ?_⟩
  intro τ LL' τ' hτ lam J hw hJ
  obtain ⟨Jr, hJr, hcard⟩ := h5 l P AI hT E Ω A O Bw a _ hdr τ LL' τ' hτ
  obtain ⟨J', hJ', hsub⟩ := hocc P AI hT A hA O Bw hj τ LL' τ' hτ lam J hw hJ
  obtain ⟨m, n, e, hin⟩ := h1 _ _ a dd r ρ hcov
  have hR := h2 _ _ a m n e r hss
  have hcomp : (blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype =
      blockRep (a := fun _ : Fin m => a) e fun _ => r.comp (Dec (F := E) A).subtype := by
    ext g i j
    rfl
  have hjR : IsJumpsAt P Bw ((blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype) τ
      (∑ _ : Fin m, Jr) := by
    rw [hcomp]
    exact GlobalTheory.BlockSum.isJumpsAt_blockRep P Bw e hτ fun _ => hJr
  have hle : J' ≤ ∑ _ : Fin m, Jr :=
    (h3 E Ω l dd n ρ _ hR hin ι w P AI hT A hA O Bw hj).2 τ _ _ hjR hJ'
  have hJeq : J = (wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJ.trans (wtJumps_val lam).symm)
  have hnd : J.Nodup := hJeq ▸ (wtJumps lam).nodup
  have hJc : J.card = a := by rw [hJeq]; exact card_wtJumps lam
  have hss' : J ⊆ Jr := fun j hjJ => by
    obtain ⟨_, -, hj'⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hle (hsub j hjJ))
    exact hj'
  have hJJ : J = Jr :=
    Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 hss') (by rw [hcard, hJc])
  rw [hJJ]
  exact hJr
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
end

section

namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem satPol_facts {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (s : Multiset ℂ) :
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).Monic ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).natDegree = Multiset.card s ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).coeff 0 = ι.symm ((-1) ^ Multiset.card s * s.prod) ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).map ι.toRingHom = (s.map fun b => X - C b).prod := by
  refine ⟨(monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b).map _, ?_, ?_, ?_⟩
  · rw [natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card]
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    have : (s.map ((fun p : ℂ[X] => eval 0 p) ∘ fun b => X - C b)) = s.map Neg.neg := by
      refine Multiset.map_congr rfl fun b _ => ?_
      simp
    rw [this, Multiset.prod_map_neg]
    rfl
  · rw [Polynomial.map_map]
    have : ι.toRingHom.comp ι.symm.toRingHom = RingHom.id ℂ := by
      ext z
      simp
    rw [this, Polynomial.map_id]

theorem UpperTheory.Gal.Int.Div.divOne_of :
    DivSet → DenseUs → DetFrob → InFacts → SepPin → DivOne := by
  intro hDiv hDense hDet hIn hSep E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ dd ρ hV
  obtain ⟨hc, hs, ⟨X, hX⟩, hr⟩ := hV
  have hcard : ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), SatU U w B →
      Multiset.card (algSat a (normV w) B) = a := by
    rintro w B ⟨σ, -, hB⟩
    have h : Multiset.card (algSat a (normV w) B) = Multiset.card B := by
      unfold algSat
      simp
    rw [h]
    exact GlobalTheory.LFun.HasSatGL.card hB
  have hD := (hDense E Ω l a d hd U hU X).preimage (Homeomorph.inv (G E Ω)).isOpenMap
  obtain ⟨r, hrc, hrs, hin, hco, hop, hde⟩ := hDiv E Ω l a dd ρ hc hs hr ψ hψ.1 (hD.mono (by
    rintro g ⟨w, hw, hu, hl, ⟨B, hB⟩, A, hA, hf⟩
    have hf' : IsFrob A (normV w) g⁻¹ := hf
    obtain ⟨q1, q2, q3, -⟩ := satPol_facts ι (algSat a (normV w) B)
    rw [hcard w B hB] at q2 q3
    refine ⟨_, q1, q2, ?_, ?_⟩
    · have := (hX w hw hu hl B hB A hA).2 g⁻¹ hf'
      rwa [inv_inv] at this
    · have h := (hDet E Ω l ι a U ψ hψ w hu.1 hl B hB A hA).2 g⁻¹ hf'
      rw [inv_inv] at h
      rw [q3]
      apply ι.injective
      have h1 : ((-1 : ℂ) ^ a) * (-1) ^ a = 1 := by
        rw [← mul_pow]; simp
      simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply]
      rw [h, ← mul_assoc, h1, one_mul]))
  refine ⟨r, ⟨hrc, hrs, (fun g : G E Ω => g⁻¹) ⁻¹' {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable}, X,
    hop.preimage continuous_inv, hde.preimage (Homeomorph.inv (G E Ω)).isOpenMap, ?_⟩, hin, hco⟩
  intro w hw hu hl B hB A hA
  have hE := hX w hw hu hl B hB A hA
  have hF := hIn (G E Ω) (Qbar l) a dd r ρ hin
  refine ⟨fun s hs' => hF.2.1 s (hE.1 s hs'), fun s hf hsV => ?_⟩
  obtain ⟨q1, q2, -, q4⟩ := satPol_facts ι (algSat a (normV w) B)
  rw [hcard w B hB] at q2
  rw [hSep (Qbar l) a _ _ q1 q2 (hF.2.2 s⁻¹ _ (hE.2 s hf)) hsV, q4]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.isoMove_of :
    IsoMove := by
  intro Γ k _ _ a d r r' ρ ⟨u, hu⟩
  set U : Matrix (Fin a) (Fin a) k := (u : Matrix (Fin a) (Fin a) k) with hUdef
  set V : Matrix (Fin a) (Fin a) k := ((u⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) with hVdef
  have hVU : V * U = 1 := by
    simp only [hUdef, hVdef]
    exact Units.inv_mul u
  have hUV : U * V = 1 := by
    simp only [hUdef, hVdef]
    exact Units.mul_inv u
  have hr' : ∀ x, (r' x : Matrix (Fin a) (Fin a) k) = U * (r x : Matrix (Fin a) (Fin a) k) * V := by
    intro x
    rw [hu x]
    rfl
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 ⟨u⁻¹, rfl⟩
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A * V, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_left_of_isUnit_det V A hVdet, hA]
    · rw [hr' g, ← Matrix.mul_assoc, h g]
      calc A * (r g : Matrix (Fin a) (Fin a) k) * V
          = A * (1 * (r g : Matrix (Fin a) (Fin a) k)) * V := by rw [Matrix.one_mul]
        _ = A * V * (U * (r g : Matrix (Fin a) (Fin a) k) * V) := by
            rw [← hVU]; simp only [Matrix.mul_assoc]
  · rintro ⟨m, B, hB, h⟩
    have hk : ∀ X Y : Matrix (Fin a) (Fin a) k,
        Matrix.kronecker (X * Y) (1 : Matrix (Fin m) (Fin m) k)
          = Matrix.kronecker X (1 : Matrix (Fin m) (Fin m) k) * Matrix.kronecker Y (1 : Matrix (Fin m) (Fin m) k) := by
      intro X Y
      have := Matrix.mul_kronecker_mul X Y (1 : Matrix (Fin m) (Fin m) k) (1 : Matrix (Fin m) (Fin m) k)
      simpa using this
    have h1 : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) = 1 :=
      Matrix.one_kronecker_one
    set P := Matrix.kronecker U (1 : Matrix (Fin m) (Fin m) k) with hP
    set Q := Matrix.kronecker V (1 : Matrix (Fin m) (Fin m) k) with hQ
    have hQP : Q * P = 1 := by rw [hQ, hP, ← hk, hVU, h1]
    have hPQ : P * Q = 1 := by rw [hQ, hP, ← hk, hUV, h1]
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
    refine ⟨m, P * B, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_right_of_isUnit_det P B hPdet, hB]
    · have hc : Matrix.kronecker (U * (r g : Matrix (Fin a) (Fin a) k) * V) (1 : Matrix (Fin m) (Fin m) k)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q := by
        rw [hk, hk]
      rw [hr' g, hc]
      calc P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q * (P * B)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * ((Q * P) * B) := by
            simp only [Matrix.mul_assoc]
        _ = P * (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * B) := by
            rw [hQP, Matrix.one_mul, Matrix.mul_assoc]
        _ = P * B * (ρ g : Matrix (Fin d) (Fin d) k) := by
            rw [h g, Matrix.mul_assoc]
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divUniq_of :
    DenseUs → DivUniq := by
  classical
  intro hD E Ω _ _ _ _ _ _ l _ ι a d hd U hU r r' hr hr'
  obtain ⟨hc, hs, V, X, hVo, hVd, h⟩ := hr
  obtain ⟨hc', hs', V', X', hVo', hVd', h'⟩ := hr'
  have hS := hD E Ω l a d hd U hU (X ∪ X')
  have hI := (hS.inter_of_isOpen_right hVd hVo).inter_of_isOpen_right hVd' hVo'
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (hI.preimage (Homeomorph.inv (G E Ω)).isOpenMap) ?_
  rintro g ⟨⟨⟨w, hw, hus, hl, ⟨B, hB⟩, A, hP, hF⟩, hV⟩, hV'⟩
  have hwX : w ∉ X := fun hx => hw (Finset.mem_union_left _ hx)
  have hwX' : w ∉ X' := fun hx => hw (Finset.mem_union_right _ hx)
  have e1 := (h w hwX hus hl B hB A hP).2 g⁻¹ hF hV
  have e2 := (h' w hwX' hus hl B hB A hP).2 g⁻¹ hF hV'
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
end
