module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle019
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameParahoric

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem val_det_sub_one_lt {m : Type} [Fintype m] [LinearOrder m] (A : Matrix m m 𝒪[k])
    (hl : ∀ i j, j < i → valuation k (algebraMap 𝒪[k] k (A i j)) < 1)
    (hd : ∀ i, valuation k (algebraMap 𝒪[k] k (A i i) - 1) < 1) :
    valuation k ((A.map (algebraMap 𝒪[k] k)).det - 1) < 1 := by
  have h1 : (A.map (IsLocalRing.residue 𝒪[k])).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := (residue_eq_zero_iff_val_lt (A i i - 1)).2 (by simpa using hd i)
      rw [map_sub, map_one, sub_eq_zero] at this
      simpa using this
    · intro i j hij
      exact (residue_eq_zero_iff_val_lt _).2 (hl i j hij)
  have h2 : IsLocalRing.residue 𝒪[k] (A.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    simpa using h1
  have := (residue_eq_zero_iff_val_lt _).1 h2
  rwa [map_sub, map_one, RingHom.map_det] at this

theorem isIwVec_of_isParahoricVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V) (hχ : IsTame χ) (hv : IsParahoricVec χ π v) :
    IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  have hlt : ∀ (i : Fin t) (j : Fin r), Fin.castAdd t j < Fin.natAdd r i := by
    intro i j
    rw [Fin.lt_iff_val_lt_val]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  refine ⟨fun h hK hl hd => ?_, fun s hs => ?_⟩
  · obtain ⟨h₀, hh⟩ := hK
    have hval : ∀ i j, h.val i j = algebraMap 𝒪[k] k (h₀.val i j) := by
      intro i j
      rw [← hh]
      rfl
    have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) =
        (h₀.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (algebraMap 𝒪[k] k) := by
      ext i j
      simp [hval]
    have hdet : valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
      rw [hsub]
      refine val_det_sub_one_lt _ (fun i j hij => ?_) (fun i => ?_)
      · simpa [hval] using hl (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
      · simpa [hval] using hd (Fin.natAdd r i)
    have hne : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdet
      exact lt_irrefl _ hdet
    have hu : χ (Units.mk0 _ hne) = 1 := hχ _ (by simpa using hdet)
    rw [hv h ⟨h₀, hh⟩ (fun i j => hl _ _ (hlt i j)) (Units.mk0 _ hne) rfl, hu]
    simp
  · have hD : ((∏ j : Fin t, s (Fin.natAdd r j) : kˣ) : k) =
        ((diagT k (Fin (r + t)) s).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
      rw [val_diagT, Matrix.submatrix_diagonal _ _ (Fin.natAdd_injective _ _), Matrix.det_diagonal]
      simp [Units.coe_prod]
    have hlow : ∀ (i : Fin t) (j : Fin r),
        valuation k ((diagT k (Fin (r + t)) s).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
      intro i j
      rw [val_diagT, Matrix.diagonal_apply_ne _ (hlt i j).ne']
      simp
    rw [hv _ (iwahori_le_KO k (Fin (r + t)) (diagT_mem_iwahori hs)) hlow _ hD]
    congr 2
    rw [torusChar_apply, Fin.prod_univ_add, map_prod]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.TameParahoric
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem residue_map_equiv {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R ≃+* R') {a b : R} (h : IsLocalRing.residue R a = IsLocalRing.residue R b) :
    IsLocalRing.residue R' (φ a) = IsLocalRing.residue R' (φ b) := by
  have h' : IsLocalRing.residue R (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h') ((isUnit_map_iff φ _).1 hu)

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (Formalism.AUTREP.GAf L n)) (Dset : Set (Formalism.AUTREP.GAf L n))
    (hfin : ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Dset).Finite)
    (c : ℂ) (f f' : Formalism.AUTREP.GAf L n → W) :
    Formalism.L2.NG.heckeD J Dset (c • f + f') = c • Formalism.L2.NG.heckeD J Dset f + Formalism.L2.NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : Formalism.AUTREP.GAf L n → W,
      Function.support (fun cc : Formalism.AUTREP.GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : Formalism.AUTREP.GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (Formalism.AUTREP.GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dite_eq_right]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply, Pi.smul_apply]
  simp only [Formalism.L2.NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem cls_eq_of_residue : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : Algebra.adjoin O S →ₐ[O] O), (∀ a (h : a ∈ S), IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin h⟩) = IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin h⟩)) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  first
  | exact @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | (apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators ..)

theorem pt_of_eigvec : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Set (Module.End K V)) (e : V), e ≠ 0 → Function.Injective (algebraMap O K) → (∀ a ∈ S, ∃ c : O, a e = algebraMap O K c • e) → ∃ ψ : Algebra.adjoin O S →ₐ[O] O, (∀ t : Algebra.adjoin O S, (t : Module.End K V) e = algebraMap O K (ψ t) • e) ∧ e ∈ Formalism.L2.NCov.W (Algebra.adjoin O S) (Formalism.L2.NCov.pt ψ) := by
  intro O K V _ _ _ _ _ _ _ S e he hinj hS
  have key : ∀ t ∈ Algebra.adjoin O S, ∃ c : O, t e = algebraMap O K c • e := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha => exact hS a ha
    | algebraMap r => exact ⟨r, by rw [Formalism.L2.NCov.algebraMap_end_eq]; simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 + c2, by rw [LinearMap.add_apply, h1, h2, map_add (f := _), add_smul]⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 * c2, by rw [Module.End.mul_apply, h2, map_smul, h1, smul_smul, map_mul, mul_comm]⟩
  choose f hf using fun t : Algebra.adjoin O S => key t t.2
  have uniq : ∀ c c' : O, algebraMap O K c • e = algebraMap O K c' • e → c = c' :=
    fun c c' hcc => hinj (smul_left_injective K he hcc)
  have f1 : f 1 = 1 := uniq _ _ (by rw [← hf 1, map_one, one_smul]; rfl)
  have fm : ∀ s t, f (s * t) = f s * f t := fun s t => uniq _ _ (by
    rw [← hf (s * t), map_mul, mul_comm, mul_smul, ← hf s, ← map_smul, ← hf t]; rfl)
  have f0 : f 0 = 0 := uniq _ _ (by rw [← hf 0, map_zero, zero_smul]; rfl)
  have fa : ∀ s t, f (s + t) = f s + f t := fun s t => uniq _ _ (by
    rw [← hf (s + t), map_add (f := _), add_smul, ← hf s, ← hf t]; rfl)
  have fc : ∀ r, f (algebraMap O (Algebra.adjoin O S) r) = r := fun r => uniq _ _ (by
    rw [← hf]
    show (algebraMap O (Module.End K V) r) e = _
    rw [Formalism.L2.NCov.algebraMap_end_eq]; simp)
  let ψ : Algebra.adjoin O S →ₐ[O] O :=
    { toFun := f, map_one' := f1, map_mul' := fm, map_zero' := f0, map_add' := fa, commutes' := fc }
  refine ⟨ψ, fun t => hf t, ?_⟩
  refine (Submodule.mem_iInf _).2 fun t => ?_
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.L2.NCov.pt]
  rw [hf t]
  exact sub_self _

theorem descent : ∀ {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type} (Mg : G → Matrix ι ι K) (d : ι → C), d ≠ 0 → (∀ g, Matrix.mulVec ((Mg g).map φ) d = 0) → ∃ c : ι → K, c ≠ 0 ∧ ∀ g, Matrix.mulVec (Mg g) c = 0 := by
  intro K C _ _ φ ι _ G Mg d hd hdg
  classical
  by_contra hne
  push_neg at hne
  let kerS : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kerS s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kerS s) ≤ Module.finrank K (kerS s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hbot : kerS s = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    by_contra hc0
    obtain ⟨g, hg⟩ := hne c hc0
    have hins : kerS (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kerS s := by
      simp only [kerS, Finset.iInf_insert]
    have hle : kerS (insert g s) ≤ kerS s := by rw [hins]; exact inf_le_right
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
    have hc' : c ∈ kerS (insert g s) := heq ▸ hc
    rw [hins] at hc'
    exact hg (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hc').1)
  let R : Matrix (↥s × ι) ι K := fun p b => Mg p.1.1 p.2 b
  have hinjR : Function.Injective (Matrix.toLin' R) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [← hbot]
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    funext a
    have hc' : Matrix.mulVec R c = 0 := by rw [← Matrix.toLin'_apply]; exact LinearMap.mem_ker.1 hc
    have := congrFun hc' (⟨g, hg⟩, a)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, R] using this
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' R) (LinearMap.ker_eq_bot.2 hinjR)
  have hLR : LinearMap.toMatrix' Ψ * R = 1 := by
    have := congrArg LinearMap.toMatrix' hΨ
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hLRC : (LinearMap.toMatrix' Ψ).map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, hLR, Matrix.map_one φ φ.map_zero φ.map_one]
  have hRd : Matrix.mulVec (R.map φ) d = 0 := by
    funext p
    have := congrFun (hdg p.1.1) p.2
    simp only [Matrix.mulVec, dotProduct] at this
    exact this
  apply hd
  calc d = Matrix.mulVec ((LinearMap.toMatrix' Ψ).map φ * R.map φ) d := by rw [hLRC, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRd, Matrix.mulVec_zero]

theorem coeff_monic_poly_sum {R : Type} [Semiring R] (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (c : ℕ → R) :
    (X ^ n + ∑ k' ∈ Finset.Icc 1 n, C (c k') * X ^ (n - k')).coeff (n - k) = c k := by
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [coeff_C_mul_X_pow, if_neg]
    rw [Finset.mem_Icc] at hb
    omega
  · intro hk
    exact absurd (Finset.mem_Icc.2 ⟨hk1, hk2⟩) hk

theorem coeff_extract : ∀ {O : Type} [CommRing O] [IsLocalRing O] (ι : O →+* ℂ), Function.Injective ι → ∀ (n q : ℕ), IsUnit (q : O) → ∀ (p : O[X]) (lam : ℕ → ℂ) (t : ℕ → O), p.map ι = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (n - k) → p.map (IsLocalRing.residue O) = (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) * t k) * X ^ (n - k)).map (IsLocalRing.residue O) → ∀ k, 1 ≤ k → k ≤ n → ∃ a : O, ι a = lam k ∧ IsLocalRing.residue O a = IsLocalRing.residue O (t k) := by
  intro O _ _ ι hι n q hq p lam t h1 h2 k hk1 hk2
  set u : O := (-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) with hu_def
  have hu : IsUnit u := ((isUnit_one.neg).pow k).mul (hq.pow _)
  have e1 : ι (p.coeff (n - k)) = ι u * lam k := by
    have := congrArg (fun P : ℂ[X] => P.coeff (n - k)) h1
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1) ^ k' * (q : ℂ) ^ (k' * (k' - 1) / 2) * lam k')]
    simp [u]
  have e2 : IsLocalRing.residue O (p.coeff (n - k)) = IsLocalRing.residue O (u * t k) := by
    have := congrArg (fun P : (IsLocalRing.ResidueField O)[X] => P.coeff (n - k)) h2
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1 : O) ^ k' * (q : O) ^ (k' * (k' - 1) / 2) * t k')]
  refine ⟨↑hu.unit⁻¹ * p.coeff (n - k), ?_, ?_⟩
  · rw [map_mul, e1, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
  · rw [map_mul, e2, ← map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]

theorem normV_unit : ∀ (D : D7) (i : D.nd.Loc) (w : PlE D.host), w ∉ placesOver D.host.E (D.nd.l i) → IsUnit (((normV w : ℕ) : D.nd.O i)) := by
  intro D i w hw
  classical
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hN : ¬ (D.nd.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : D.nd.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := hu.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  rwa [map_natCast] at this

end GlobalTheory.PtLocalEig
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

end GlobalTheory.InertialTypes
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

end Glob

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end Main

end GlobalTheory.TwistLG
end
end
