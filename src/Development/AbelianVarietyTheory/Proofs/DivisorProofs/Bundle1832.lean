module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Formalism.LocalToGlobal.Columns.Bundle032
import Formalism.LocalToGlobal.Columns.Bundle031
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle129
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.BasicNotions MvPolynomial
open scoped Matrix

namespace GlobalTheory.NabBC

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K]

theorem mem_localization_of_mem' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L : Submodule R W} {x : W} (h : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩

abbrev vmap {n : ℕ} (f : K₀ →+* K) (x : Fin n → K₀) : Fin n → K := fun a => f (x a)

theorem vmap_add {n : ℕ} (f : K₀ →+* K) (x y : Fin n → K₀) : vmap f (x + y) = vmap f x + vmap f y := by
  funext a; simp [vmap]

theorem vmap_smul {n : ℕ} (f : K₀ →+* K) (r : 𝓞 K₀) (x : Fin n → K₀) :
    vmap f (r • x) = RingOfIntegers.mapRingHom f r • vmap f x := by
  funext a
  change f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)
  rw [map_mul]
  rfl

theorem span_image_span {n : ℕ} (f : K₀ →+* K) (S : Set (Fin n → K₀)) :
    Submodule.span (𝓞 K) (vmap f '' (Submodule.span (𝓞 K₀) S : Set (Fin n → K₀))) =
      Submodule.span (𝓞 K) (vmap f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : vmap f (0 : Fin n → K₀) = 0 := by funext a; simp [vmap]
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [vmap_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [vmap_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localization_span_image_le {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {A B : Submodule (𝓞 K₀) (Fin n → K₀)} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀)))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
  have key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := h ha
    exact show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from
      ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := key hsx
  exact show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from
    ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩

theorem span_vmap_colLat {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    Submodule.span (𝓞 K) (vmap f '' (colLat C : Set (Fin n → K₀))) = colLat (Formalism.UG.bc f C) := by
  unfold colLat
  rw [span_image_span, ← Set.range_comp]
  congr 1

theorem isBasisAt_span_vmap {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {L : Submodule (𝓞 K₀) (Fin n → K₀)} {C : GL (Fin n) K₀} (hC : IsBasisAt w₀ L C) :
    IsBasisAt w (Submodule.span (𝓞 K) (vmap f '' (L : Set (Fin n → K₀)))) (Formalism.UG.bc f C) := by
  unfold IsBasisAt at hC ⊢
  rw [← span_vmap_colLat]
  have h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C) := hC ▸ fun x hx => mem_localization_of_mem' _ hx
  have h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L := hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx
  exact le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)

theorem tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K) (emb : ι → E →+* K₀) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) :
    tauLat (fun τ => f.comp (emb τ)) τ M = Submodule.span (𝓞 K) (vmap f '' (tauLat emb τ M : Set (Fin n → K₀))) := by
  unfold tauLat
  rw [span_image_span, Set.image_image]
  rfl

theorem invTr_bc {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    inside₂ K n (Formalism.UG.bc f C) = Formalism.UG.bc f (inside₂ K₀ n C) := by
  apply Units.ext
  change (((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]
  rfl

theorem isBasisAt_dualFr_tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (τ : ι) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    (C : GL (Fin n) K₀) (hC : IsBasisAt w₀ (tauLat emb τ M) C) :
    IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (inside₂ K₀ n C)) := by
  rw [← invTr_bc]
  refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_
  rw [tauLat_comp]
  exact isBasisAt_span_vmap f w₀ w hw hC

theorem nabStd_le_span_map {ι : Type} [Fintype ι] {n : ℕ} (f : K₀ →+* K) (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

theorem map_smul_int {σ : Type} (f : K₀ →+* K) (t : 𝓞 K₀) (P : MvPolynomial σ K₀) :
    RingOfIntegers.mapRingHom f t • MvPolynomial.map f P = MvPolynomial.map f (t • P) := by
  ext m
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change ((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)
  rw [map_mul]
  rfl

theorem mem_localization_span_map {E ι : Type} [Field E] [NumberField E] [Fintype ι] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n}
    (hF : F ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))) := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  set N' := Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'
  have key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))),
      actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' := by
    intro H hH
    refine (Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap
      ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH
    rintro _ ⟨g, hg, rfl⟩
    show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'
    rw [← GlobalTheory.ValCmp.use₂]
    have hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) := by
      rw [L0]
      exact Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)
    obtain ⟨t, ht, htg⟩ := hg'
    refine ⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩
    have e := map_smul_int f t (actP lam B₀ g)
    refine (congrArg (· ∈ N') e).mpr ?_
    exact Submodule.subset_span ⟨_, htg, rfl⟩
  have hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :=
    mem_localization_of_mem' _ hF
  rw [L1] at hF'
  obtain ⟨G, ⟨s, hs, hsG⟩, rfl⟩ := hF'
  obtain ⟨t, ht, htG⟩ := key _ (nabStd_le_span_map f lam hsG)
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  convert htG using 1
  rw [mul_smul]
  congr 1
  exact (((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm

theorem nabBaseChange : ∀ (E K₀ K ι : Type) [Field E] [NumberField E] [Field K₀] [NumberField K₀]
    [Field K] [NumberField K] [Fintype ι] (n : ℕ) (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E M →
    nabAtr (fun τ => f.comp (emb τ)) lam M ≤
      Submodule.span (𝓞 K) {y : VV K lam | ∃ x ∈ nabAtr emb lam M,
        (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} := by
  intro E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF
  obtain ⟨-, -, hV⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) :=
    GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF
  have hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) ''
      {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} =
      MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)) := by
    ext P
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      exact ⟨x.1, hx, hxy.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ VV K₀ lam := hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx
      exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩
  rw [← hS, ← Submodule.map_span] at hP
  obtain ⟨y, hy, hyF⟩ := hP
  have e : y = F := Subtype.ext hyF
  rwa [← e]

end GlobalTheory.NabBC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section
namespace GlobalTheory.LowSpan

theorem span_translates_eq_top : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (v : M.Vec), IsExtVec M v → ∀ τ : D.what₂.Tau, Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) → Submodule.span ℂ {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ)} = ⊤ := by
  intro D V S M v hv τ hK
  obtain ⟨_hfd, hst, hirr, -, -⟩ := hK
  obtain ⟨-, -, hU, -⟩ := M.ds τ
  obtain ⟨S₀, hS₀, hS₀sm⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M τ
  have hle : S₀ ≤ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) :=
    le_sSup (s := {T | Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T}) hS₀
  have hS₀ne : S₀ ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hS₀.2.2.2.1
    intro h; rw [h] at hw; exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have hLsm : Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
    rcases hirr S₀ hle hS₀.2.1 with h | h
    · exact absurd h hS₀ne
    · rw [← h]; exact hS₀sm

  set L := Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) with hLdef
  set v0 : M.H τ := ((v τ : M.sm τ) : M.H τ) with hv0def
  have hv0L : v0 ∈ L := (hv τ).2.1
  have hv00 : v0 ≠ 0 := by
    intro h; have h1 := (hv τ).1; rw [← hv0def, h, norm_zero] at h1; exact zero_ne_one h1
  set T : Set (M.H τ) := {x | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), x = M.σ τ k v0} with hTdef
  have hWL : Submodule.span ℂ T ≤ L := by
    rw [Submodule.span_le]; rintro _ ⟨k, hk, rfl⟩; exact hst k hk _ hv0L
  have hWst : Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) (Submodule.span ℂ T) := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨g * k, Formalism.REAL.Kset_mul _ hg hk, ?_⟩
      rw [hU.1.2 g (kset_uj hg) k (kset_uj hk)]; rfl
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h1K : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := by
    have := diag_mem (ε := M.ε τ) (fun _ => (0 : ℝ))
    simpa using this
  have hW0 : Submodule.span ℂ T ≠ ⊥ := by
    intro h
    have : v0 ∈ Submodule.span ℂ T := Submodule.subset_span ⟨1, h1K, by rw [hU.1.1]; rfl⟩
    rw [h] at this; exact hv00 ((Submodule.mem_bot ℂ).1 this)
  have hWeq : Submodule.span ℂ T = L := (hirr _ hWL hWst).resolve_left hW0
  let f : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hf : Function.Injective f := (M.sm τ).injective_subtype.comp (lowT M τ).injective_subtype
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_span, Submodule.map_top]
  have himg : f '' {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k v0} = T := by
    ext x; constructor
    · rintro ⟨u, ⟨k, hk, hu⟩, rfl⟩; exact ⟨k, hk, hu⟩
    · rintro ⟨k, hk, rfl⟩
      have hxL : M.σ τ k v0 ∈ L := hst k hk _ hv0L
      exact ⟨⟨⟨_, hLsm hxL⟩, hxL⟩, ⟨k, hk, rfl⟩, rfl⟩
  rw [himg, hWeq]
  ext y; constructor
  · intro hy; exact ⟨⟨⟨y, hLsm hy⟩, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

end GlobalTheory.LowSpan
end
end

section

open NumberField Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_eq_of_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) →
    ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      (∀ w : WO V W, w.map (finPart D) = 0 → f w = f' w) → f = f' := by
  intro D ψ V W _ f f' hf hf' h
  have h0 : f + (-1 : ℂ) • f' = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real
    (GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul (-1) hf')) fun w hw => by
      rw [Pi.add_apply, Pi.smul_apply, h w hw, neg_one_smul, add_neg_cancel]
  rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0

end GlobalTheory.AdTh
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.base_theta_vector_is_vacuum_even_ranks : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  first | exact @GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | exact GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | (intros; apply GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulus

theorem norm_eq_one_of_locK {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ}
    {j : Fin m} {χ : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (h : IsMu0 Ch σ₀ e j χ)
    (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ) (y : X.K) (hy : σ₀ y = ((χ.locK P x : ℂˣ) : ℂ)) (σ : X.K →+* ℂ) :
    ‖σ y‖ = 1 := by
  have h0 : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (hPr.g_prime 0).ne_zero) (by exact_mod_cast (hPr.g_prime 1).ne_zero)
  obtain ⟨M, z, hM, -, -, hz⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E χ
    (divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E))) (GlobalTheory.CharVal.productRule χ)
    (fun v hv => h.unr v fun i hi => hv ((Formalism.L2.Col.mem_divs h0 v).2 (by
      fin_cases i
      exacts [v.asIdeal.mul_mem_right _ hi, v.asIdeal.mul_mem_left _ hi]))) h.tame P x
  obtain ⟨n, -, hn⟩ := h.inf
  have hz' := congrArg Units.val hz
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hn z, ← hy, Units.val_one] at hz'
  have hsq : ∀ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ 2 =
      σ₀ (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) := by
    intro τ
    have h1 : X.embC σ₀ τ z ≠ 0 := (map_ne_zero _).2 z.ne_zero
    have h2 := hX.conjE (X.embC σ₀ τ) z
    rw [map_div₀]
    change _ = X.embC σ₀ τ z / X.embC σ₀ τ (star (z : X.E))
    rw [h2, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h1]
  have key : y ^ (M * 2) * ∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ = 1 := by
    apply σ₀.injective
    rw [map_one, map_mul, map_pow, map_prod, pow_mul]
    have h3 : ∏ τ, σ₀ ((X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ) =
        (∏ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ n τ) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, ← hsq, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [h3, ← mul_pow, hz', one_pow]
  have h4 : ‖σ (∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ)‖ = 1 := by
    rw [map_prod, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 : ‖(σ.comp (X.emb τ)) z‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 z.ne_zero)
    have h2 := hX.conjE (σ.comp (X.emb τ)) z
    rw [RingHom.comp_apply] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rw [map_zpow₀, norm_zpow, map_div₀, norm_div, h2, Complex.norm_conj, div_self h1, one_zpow]
  have h5 := congrArg (fun t => ‖σ t‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, h4, mul_one, map_one, norm_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h5

theorem norm_muInvDet {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs)
    (ht : Ch.Tied G.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j < R.m) {n : ℕ}
    (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ) :
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr)‖ = 1 := by
  have hU := fun P x y hy => norm_eq_one_of_locK hX hPr (ht.mu0 ⟨j, hj⟩) P x y hy σ
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      ‖σ (Ch.muVal ⟨j, hj⟩ P : X.K)‖ = 1 := fun P hP =>
    hU P (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have hfin := GlobalTheory.CharVal.finOrder_tup mu
  have h1 : ∀ P : rowSG Pr sel mu, ‖σ (cst.muq (j + 1) P)‖ = 1 := by
    intro P
    have hq : ‖σ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
      GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
    have h1 := hL.muqG j hj P (hS P) (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
    have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
        (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
      rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
    have h3 := hU P.1 _ _ h2
    rwa [map_inv₀, map_mul, norm_inv, norm_mul, hq, mul_one, inv_eq_one] at h3
  have h2 : ‖σ (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N)‖ = 1 := by
    unfold muOff
    refine finprod_induction (fun x => ‖σ x‖ = 1) (by simp)
      (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · simp
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dite_eq_left hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul, norm_inv, norm_inv,
        hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX hPr hsel hv),
        GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
      simp
  rw [muInvDet, map_mul, norm_mul, h2, one_mul, map_prod, norm_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (j + 1) P) _
    ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _)
      (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2) (Units.ne_zero _)
  rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, h1, GlobalTheory.GO.norm_map_of_finOrder _ hζ, one_zpow, one_mul]

end GlobalTheory.ScalarModulus
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.admissibleComplementTwo_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  first | exact @GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | exact GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | (intros; apply GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize <;> assumption)
end
