module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.MemMaxIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AbsPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DefEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.NotDvdIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.PresQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FrobIn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Choice
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem not_over {Ω : Type} [Field Ω] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : q ≠ p) {A : ValuationSubring Ω}
    (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := fun hq' => by
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 e)
  have h1 : A.valuation ((a : Ω) * (q : Ω) + (b : Ω) * (p : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hq'
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A b))) hA
  have h2 : (a : Ω) * (q : Ω) + (b : Ω) * (p : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

section
variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

private theorem uM_map {Y : M4 R} (h : Y ∈ uM R) : Y.map f ∈ uM R' := by
  refine ⟨fun i j e => by rw [Matrix.map_apply, h.1 i j e, map_zero], ?_⟩
  have e : adj Y = -Y := h.2
  show adj _ = -_
  rw [(grp R).2.2.2.2.2.1, e]
  ext i j
  simp

private theorem blk_map {Y : M4 R} (h : IsBlock Y) : IsBlock (Y.map f) := fun i j e => by
  rw [Matrix.map_apply, h i j e, map_zero]

private theorem rep_eq {Γ : Type} [Group Γ] (r : Γ →* M4 R) (g : Γ) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem adj_mapMatrix (Y : M4 R) : adj (f.mapMatrix Y) = f.mapMatrix (adj Y) := (grp R).2.2.2.2.2.1 R' f Y

private theorem eAB_map : (eAB R).map f = eAB R' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eAB]

end

theorem UpperTheory.V.Ws.bl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      Submodule.span 𝔞.K (Set.range fun g => (mapRep 𝔞.toK r g).submatrix ixA ixA) = ⊤ →
      ∃ r' u', KPair D 𝔞 r' u' ∧ BlockExt (mapRep 𝔞.toK r') ∧ ∀ g, (r' g).charpoly = (r g).charpoly := by
  intro hP Ω _ _ _ l hl c D hD 𝔞 r u hK hB hsp
  obtain ⟨hpos, h2, A, _, _, _, f, r₁, u₁, hf, hr, hu, hlA, hb⟩ := toGlobalTheory D hD 𝔞 r u hK hB
  haveI := hf.fin
  haveI := hf.loc
  obtain ⟨r', z, y, e, hc, hz, hy, hm, hzc, hN, hfl, hne⟩ := cocA hP _ _ _ _ hpos A r₁ u₁ hf.complete hlA hb
  have hinj : Function.Injective (f.mapMatrix : M4 A →+* M4 𝔞.V) := Matrix.map_injective hf.inj
  have er : ∀ g, r g = f.mapMatrix (r₁ g) := fun g => by rw [← hr]; rfl
  have eu : u = f.mapMatrix u₁ := hu.symm
  have eV : ∀ g, mapRep f r' g = (1 + (z g).map f) * r g := fun g => by
    rw [rep_eq, e, map_mul, map_add (f := _), map_one, er]; rfl
  have hzV : ∀ g, (z g).map f ∈ uM 𝔞.V := fun g => uM_map f (hz g)
  have hyV := uM_map f hy
  have kill : ∀ g (B : ValuationSubring Ω), ¬ B.valuation (l : Ω) < 1 → g ∈ Ine (F := ℚ) B → r g = 1 → mapRep f r' g = 1 :=
    fun g B h1 h3 h4 => by
      have h5 : r₁ g = 1 := hinj (by rw [← er, h4, map_one])
      rw [eV, hN g ⟨h5, B, h1, h3⟩, h4]
      simp
  have fl : ∀ s ∈ D.Gp l, IsUp (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u)) ∧
      ∀ i, (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u) : M4 𝔞.V) i i = (adj u * r s * u : M4 𝔞.V) i i :=
    fun s hs => by
      rw [eV]
      refine twistFlag _ (r s) (r s⁻¹) _ _ u (hB s) (hB _) (by rw [← map_mul, inv_mul_cancel, map_one]) (hzV s) hyV hK.sp
        (hK.flag s hs) fun i j hij => ?_
      have h1 : adj u * ((z s).map f - (r s * y.map f * r s⁻¹ - y.map f)) * u =
          f.mapMatrix (adj u₁ * (z s - (r₁ s * y * r₁ s⁻¹ - y)) * u₁) := by
        rw [eu, er, er, adj_mapMatrix]
        simp only [map_mul, map_sub]
        rfl
      rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, hfl s hs i j hij, map_zero]
  have eK : ∀ g, mapRep 𝔞.toK (mapRep f r') g = (1 + ((z g).map f).map 𝔞.toK) * mapRep 𝔞.toK r g := fun g => by
    rw [rep_eq, eV, map_mul, map_add (f := _), map_one]; rfl
  have hBK : ∀ g, IsBlock (mapRep 𝔞.toK r g) := fun g => blk_map 𝔞.toK (hB g)
  have hzK : ∀ g, ((z g).map f).map 𝔞.toK ∈ uM 𝔞.K := fun g => uM_map _ (hzV g)
  refine ⟨mapRep f r', (1 - y.map f) * u, ⟨⟨A, _, _, _, f, ⟨r', fun _ => (1 - y) * u₁⟩, hf, hc, ?_⟩, fun g i j => ?_, fun g => ?_,
    fun B hA g hg h1 => ?_, fun p hp g hg => ?_, ?_, fun s hs => (fl s hs).1, fun s hs i => ?_, fun s hs i => ?_⟩,
    ⟨fun g i j h => ?_, ?_, ?_⟩, fun g => ?_⟩
  · refine PD.ext rfl (funext fun _ => ?_)
    show f.mapMatrix ((1 - y) * u₁) = _
    rw [map_mul, map_sub, map_one, eu]; rfl
  · rw [eV, add_mul, one_mul, Matrix.add_apply, add_sub_right_comm]
    refine Ideal.add_mem _ (hK.red g i j) ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (map_nonunit f _ (hm g i k))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).1 _ _ (hK.mult g)
  · exact kill g B (hA l (Finset.mem_insert_self _ _)) hg (hK.unr B hA g hg h1)
  · obtain ⟨h3, h4, -⟩ := (facts D hD).1 p hp
    exact kill g _ (not_over h3 hl.out h4.symm (hD.pl_over p h3)) hg.1 (hK.atP p hp g hg)
  · rw [sub_eq_add_neg]
    exact (twistPt _ _ _ (hB 1) (neg_mem hyV)).1 _ _ hK.sp
  · rw [(fl s hs).2]
    exact hK.char s hs i
  · rw [(fl s (Ine_le_Dec _ hs)).2]
    exact hK.inert s hs i
  · rw [eK]
    exact (twistPt _ _ _ (hBK g) (hzK g)).2.1 i j h
  · rw [show (fun g => (mapRep 𝔞.toK (mapRep f r') g).submatrix ixB ixB) = fun g => (mapRep 𝔞.toK r g).submatrix ixB ixB from
      funext fun g => by rw [eK]; exact (twistPt _ _ _ (hBK g) (hzK g)).2.2.1]
    refine spanB _ _ _ ⟨fun g => ⟨𝔞.toK (𝔞.a c (D.th g)), ?_⟩, hBK⟩ hsp
    have h1 := congrArg (𝔞.toK.mapMatrix : M4 𝔞.V →+* M4 𝔞.K) (hK.mult g)
    rw [map_mul, ← adj_mapMatrix] at h1
    refine h1.trans ?_
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rintro ⟨Y, hY, hblk⟩
    have h3 : IsUnit (2 : 𝔞.K) := by have := h2.map 𝔞.toK; rwa [map_ofNat] at this
    have h4 := noCompl _ _ (mapRep 𝔞.toK r) (fun g => ((z g).map f).map 𝔞.toK) D.cc Y h3 hBK (fun g => (hzK g).1)
      (by rw [rep_eq, er, hb.cc]; exact (congrArg (·.map 𝔞.toK) (eAB_map f)).trans (eAB_map _))
      (by rw [hzc]; ext i j; simp) hY fun g => by rw [← eK]; exact hblk g
    refine hne (funext fun g => ?_)
    ext i j
    exact hf.inj (Subtype.ext (by simpa using congrFun (congrFun (h4 g) i) j))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).2.2.2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_bot {S k : Type} [TopologicalSpace S] [CommRing k] {x : S → k} (h : AdicCont ⊥ x) : IsLocallyConstant x :=
  IsLocallyConstant.desc _ _ (h 1) ((Ideal.Quotient.mk_bijective_iff_eq_bot _).2 (pow_one _)).1

private theorem fin_res {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  obtain ⟨-, -, h1, -⟩ := dvrFacts l c.O
  haveI := h1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem inc_loc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, ((residue c'.O).comp (inc h)) x = 0 := by
  have hi : (inc h).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) (inc h) ?_
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := (Subalgebra.inclusion h).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral x
  haveI := hi.isLocalHom (Subalgebra.inclusion_injective h)
  intro x hx
  exact (residue_eq_zero_iff _).2 (map_nonunit (inc h) x hx)

private theorem count {O Γ Γb : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb]
    (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ) (hstd : Φ.Std l a)
    (π : Γ →* Γb) (hQ : Φ.Quo π) (s : PD Φ.ι Γ (ResidueField Λ)) (hs : Φ.IsRes ((residue Λ).comp a) s)
    (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) (hP : Φ.IsDef a s P)
    (tN : ∀ g ∈ Φ.N, Φ.ν g = 1) (tM : ∀ v, ∀ g ∈ Φ.Mu v, Φ.ν g = 1) (ζ : Φ.ι → Γ) (hζ : ∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v))
    (CC : Γ → Prop) (tC : ∀ g, CC g → g * g = 1 ∧ Φ.ν g = -1) (ω : Γ → ResidueField Λ)
    (tW : ∀ w, ∃ g, ((residue Λ).comp a) (Φ.rt w g) ≠ ω g) (d : ℕ)
    (ec : ∀ (ρ : Representation (ResidueField Λ) Γb (sp4 (ResidueField Λ))) (b : Φ.ι → Submodule (ResidueField Λ) (sp4 (ResidueField Λ))),
      IsOpen (ρ.ker : Set Γb) → (∀ v, ∀ g ∈ Φ.Gv v, ∀ X ∈ b v, ρ (π g) X ∈ b v) →
      (∀ f : sp4 (ResidueField Λ) →ₗ[ResidueField Λ] ResidueField Λ, (∀ g X, f (ρ (π g) X) = ω g * f X) → f = 0) →
      (∀ v, Module.finrank (ResidueField Λ) (b v) = 6) →
      (∀ g, CC g → Module.finrank (ResidueField Λ) (LinearMap.ker (ρ (π g) - 1)) ≤ 4) →
      Module.Finite (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) ∧
      Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 ρ b) + d * 6 ≤
        Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) ρ b) + d * 4) :
    ∃ m n : ℕ, HasPres Λ R m n ∧ n + 2 + 2 * d ≤ m + 2 * Nat.card Φ.ι := by
  have h2 : (2 : ResidueField Λ) ≠ 0 := hstd.ok.two.ne_zero
  obtain ⟨hstd', hs', R', _, _, _, P', hP'⟩ := X1.defEx Φ l a hstd s hs
  have hQ' : Φ.noMu.Quo π := ⟨hQ.cont, hQ.onto, hQ.ker⟩
  obtain ⟨rb, hrb, hrc⟩ := (X1.descend Φ π hQ (⊥ : Ideal (ResidueField Λ))).1 s.r hs.pair.kill hs.cont
  have hrb' : ∀ g, rb (π g) = s.r g := fun g => DFunLike.congr_fun hrb g
  have hb0 : ∀ g, ∃ x, IsGSp x (s.r g) := fun g => ⟨_, hs.pair.mult g⟩
  have hb : ∀ g, ∃ x, IsGSp x (rb g) := fun g => by
    obtain ⟨g, rfl⟩ := hQ.onto g
    rw [hrb']; exact hb0 g
  have had : ∀ g X, adSp rb hb (π g) X = adSp s.r hb0 g X := fun g X => Subtype.ext (by
    rw [adSp_val, adSp_val, ← map_inv, hrb', hrb'])
  obtain ⟨a1, a2⟩ := X1.adFacts rb hb
  obtain ⟨-, d2⟩ := X1.spDims (ResidueField Λ) h2
  obtain ⟨e1, e2⟩ := ec (adSp rb hb) (fun v => bor (s.n v)) (a1 fun i j => lc_bot (hrc i j)).1
    (fun v g hg X hX => a2 (s.n v) (π g) (hs.pair.low v).1 (by rw [hrb']; exact hs.pair.flag v g hg)
      (by rw [← map_inv, hrb']; exact hs.pair.flag v g⁻¹ (inv_mem hg)) X hX)
    (fun f hf => X1.dualZero Φ _ hstd.ok s hs.res hb0 ω tW f fun g X => by rw [← had]; exact hf g X)
    (fun v => (d2 _ (hs.pair.low v).1).1)
    (fun g hg => X1.ccDim rb hb h2 (π g) (by rw [← map_mul, (tC g hg).1, map_one]) (by
      have h1 := hs.pair.mult g
      rw [(tC g hg).2, Units.val_neg, Units.val_one, map_neg, map_one] at h1
      rw [hrb']
      exact h1))
  obtain ⟨m, p1, p2⟩ := X1.absPres Φ.noMu l a hstd' (fun _ => rfl)
    (fun g hg => by
      have h1 : Φ.noMu.ν g = 1 := tN g hg
      rw [h1, Units.val_one, map_one]) π hQ' s hs' R' P' hP' rb hb hrb e1
  obtain ⟨g, e, g1, g2⟩ := X1.muQuot Φ l a hstd s hs ζ hζ
    (fun v => by rw [tM v (ζ v) (hζ v).1, Units.val_one, map_one]) R P hP R' P' hP'
  refine ⟨_, _, X1.presQuot Λ R' R _ _ _ g e p1 g1 g2, ?_⟩
  have hc : Nat.card (Φ.ι × Fin 2) = 2 * Nat.card Φ.ι := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, mul_comm]
  rw [hc]
  have p3 : Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + 2 ≤
      m + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 (adSp rb hb) fun v : Φ.ι => bor (s.n v)) := p2
  show Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + _ + 2 + 2 * d ≤ _
  omega

theorem UpperTheory.V.Ws.x1 :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (s : PD T.ι (G T.F Ω) (ResidueField c'.O)), (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) s →
      ∀ (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R] (P : PD T.ι (G T.F Ω) R), (T.fr ∅).IsDef (inc h) s P →
      ∃ (a b : ℕ) (π : MvPowerSeries (Fin a) c'.O →ₐ[c'.O] R) (f : Fin b → MvPowerSeries (Fin a) c'.O), Function.Surjective π ∧
        RingHom.ker π = Ideal.span (Set.range f) ∧ b + 2 + 2 * T.d ≤ a + 2 * Nat.card T.ι := by
  intro hp Ω _ _ _ l _ c D T hF hD c' h s hs R _ _ _ P hP
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := inferInstance
  haveI := fin_res c'
  have hstd := (UpperTheory.V.Ws.std hp D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  haveI := hstd.char
  obtain ⟨tN, tM, tC, tW⟩ := X1.thFacts D T hF hD
  obtain ⟨S, K, Γ, _, _, _, _, _, _, π, ι, hG, hS, hpl, hQ⟩ := X1.linkT D T hF
  have hpr : UpperTheory.V.GC.Hypotheses₂ := ⟨⟨hp.loc.lf, hp.loc.lt, hp.loc.le, hp.gf, hp.ge, hp.pt⟩, hp.uo, hp.gw⟩
  choose ζ hζ using fun v : T.ι => X1.muLoc hp T.F Ω l (T.pl v) (T.ovl v)
  have ec := fun ρ b => X1.ecG hpr T.F Ω l T.realF S K Γ π hG hS T.ι ι T.pl hpl (ResidueField c'.O) (sp4 (ResidueField c'.O)) ρ b 6 4
  have tW' := tW (ResidueField c'.O) ((residue c'.O).comp (inc h)) (inc_loc h)
  have key := count (T.fr ∅) l (inc h) hstd π hQ s hs R P hP tN tM ζ hζ IsCC tC
    (fun g => (UpperTheory.V.GC.cycF T.F Ω l (ResidueField c'.O) g : ResidueField c'.O)) tW' T.d
  obtain ⟨m, n, ⟨π', f, q1, q2⟩, q3⟩ := key ec
  exact ⟨m, n, π', f, q1, q2, q3⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def blockChar {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : ∀ g, IsBlock (r g)) (ix : Fin 2 → Fin 4)
    (hix : ix = ixA ∨ ix = ixB) : H →* K where
  toFun g := ((r g).submatrix ix ix).det
  map_one' := by
    rw [map_one, Matrix.submatrix_one ix (by rcases hix with rfl | rfl <;> decide), Matrix.det_one]
  map_mul' a b := by
    rw [← Matrix.det_mul, map_mul]
    congr 1
    have ha := h a
    ext i j
    rcases hix with rfl | rfl
    · have h1 : ∀ i, r a (ixA i) 1 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixA i) 3 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero]
      rfl
    · have h1 : ∀ i, r a (ixB i) 0 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixB i) 2 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero,
        zero_add]
      rfl

theorem UpperTheory.V.Ws.nePure :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      ¬ Pure ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l hl c D hD ι 𝔞 e he r u hp hb ⟨H, M, hH, hM, hP⟩
  obtain ⟨-, f2, -, f4, -⟩ := facts D hD
  obtain ⟨a1, -, a3⟩ := f2 l (Finset.mem_insert_self _ _)
  set φ : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK with hφ
  set ρ := mapRep φ r with hρ
  have hb' : ∀ g, IsBlock (ρ g) := fun g i j h => by rw [hρ, mapRep_apply, hb g i j h, map_zero]
  have hc : Continuous ρ := smallCont 𝔞 e he _ hp.small
  haveI : CharZero 𝔞.V := φ.charZero
  have hu : adj u * u = 1 := by simpa [IsGSp] using hp.sp
  have hdet : ∀ s ∈ D.Ip l, ((r s).submatrix ixA ixA).det = 𝔞.a c (D.ps 0 s) * 𝔞.a c (D.ps 2 s) ∧
      ((r s).submatrix ixB ixB).det = 𝔞.a c (D.ps 1 s) * 𝔞.a c (D.ps 3 s) := fun s hs => by
    have h := blockDet (maximalIdeal 𝔞.V) (fun i => 𝔞.a c (D.ps i (D.sg l))) u (adj u) (r (D.sg l)) (r s) hu
      (fun i j hij hm => a3 i j hij (by
        rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at hm
        exact Ideal.Quotient.eq.2 hm))
      (hb _) (fun i j => by
        have h1 := hp.red (D.sg l) i j
        have h2 : 𝔞.a c (D.r0 (D.sg l) i j) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i (D.sg l))) i j := by
          show 𝔞.a c (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i j) = _
          rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
          split_ifs <;> simp
        rwa [h2] at h1)
      (hp.flag _ a1) (hp.char _ a1) (hb _) (hp.flag s (Ine_le_Dec _ hs))
    simpa only [hp.inert s hs] using h
  have hps : ∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, φ (𝔞.a c (D.ps i s)) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ D.wts4 i := fun i s hs => by
    rw [f4 i s hs, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact congrArg (· ^ _) (he.1 c _)
  have key : ∀ (ix : Fin 2 → Fin 4) (hix : ix = ixA ∨ ix = ixB) (i j : Fin 4),
      (∀ s ∈ D.Ip l, ((r s).submatrix ix ix).det = 𝔞.a c (D.ps i s) * 𝔞.a c (D.ps j s)) →
      ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, ((ρ g).submatrix ix ix).det =
        algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ (D.wts4 i + D.wts4 j) := fun ix hix i j h => by
    have h1 : ∀ g, r g = 1 → blockChar ρ hb' ix hix g = 1 := fun g hg => by
      have : ρ g = ρ 1 := by
        ext i j
        rw [hρ, mapRep_apply, mapRep_apply, hg, map_one r]
      rw [← map_one (blockChar ρ hb' ix hix)]
      exact congrArg (fun X : M4 _ => (X.submatrix ix ix).det) this
    refine wtChar D hD (blockChar ρ hb' ix hix) _ (hc.matrix_submatrix ix ix).matrix_det
      (fun A hA g hg h2 => h1 g (hp.unr A hA g hg h2)) (fun p h2 g hg => h1 g (hp.atP p h2 g hg)) fun s hs => ?_
    rw [pow_add, ← hps i s hs, ← hps j s hs, ← map_mul, ← h s hs.1.1, RingHom.map_det]
    rfl
  obtain ⟨U, hU, hU'⟩ := key ixA (Or.inl rfl) 0 2 fun s hs => (hdet s hs).1
  obtain ⟨W, hW, hW'⟩ := key ixB (Or.inr rfl) 1 3 fun s hs => (hdet s hs).2
  obtain ⟨p, A, f, σ, h1, h2, h3, h4, h5, h6, h7⟩ := frobIn Ω l (H ⊓ (U ⊓ W)) M (hH.inter (hU.inter hW)) hM
  have h8 := pureDet (ι : PadicAlgCl l →+* ℂ) (ρ σ) (hb' σ) (hP p h1 h2 A h3 f σ h4 h5.1 h6)
  rw [hU' σ h5.2.1, hW' σ h5.2.2, h7] at h8
  simp only [map_pow, map_natCast, norm_pow, Complex.norm_natCast] at h8
  have h9 : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ (by exact_mod_cast h1.one_lt) h4.ne'
  have h10 : D.e + 1 + 1 = D.e + 0 := pow_right_injective₀ (zero_lt_one.trans h9) h9.ne' h8
  omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ent_of_map {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) {r : Γ →* M4 R} {w : ℤ × ℤ}
    (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, hw, hne⟩ := h
  refine ⟨g, i, j, hw, fun h0 => hne ?_⟩
  have e : mapRep f r g i j = f (r g i j) := rfl
  rw [e, h0, map_zero]

private theorem mapRep_eq {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (r : Γ →* M4 R) (g : Γ) :
    mapRep f r g = (r g).map f := rfl

theorem UpperTheory.V.Ws.labels :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → ∃ pr, LabOk D pr ∧ ∀ g0 : G ℚ Ω,
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) →
      ∃ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P ∧ NearSplit D pr 𝔞 P ∧ IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r) ∧
        (Star (mapRep 𝔞.toK r) → StarE P.r) := by
  intro Ω _ _ _ l _ c D hD 𝔞 r u hK
  obtain ⟨pr, hok, hunit⟩ := Lab.choice D hD 𝔞 r u hK
  refine ⟨pr, hok, fun g0 hsep => ?_⟩
  have hwinv : ∀ Y : M4 𝔞.V, wM 𝔞.V pr * (adj (wM 𝔞.V pr) * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, sp_mul_adj (wM_sp pr), Matrix.one_mul]
  obtain ⟨hs, hsep2⟩ := sg_sep hD 𝔞 pr
  have hcg := hK.cg pr
  have hconj : adj (adj (wM 𝔞.V pr) * u) * (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr) *
      (adj (wM 𝔞.V pr) * u) = adj u * r (D.sg l) * u := by
    rw [adj_mul, adj_adj]
    simp only [Matrix.mul_assoc, hwinv]
  obtain ⟨-, -, -, himp⟩ := Lab.resFlag 𝔞.V (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr)
    (adj (wM 𝔞.V pr) * u) (fun i => 𝔞.a c ((chi D pr i (D.sg l) : (c.O)ˣ) : c.O))
    (fun i => 𝔞.a c ((D.ps i (D.sg l) : (c.O)ˣ) : c.O)) (hcg _) (sp_mul (sp_adj (wM_sp pr)) hK.sp)
    (by rw [hconj]; exact hK.flag _ hs) (by rw [hconj]; exact hK.char _ hs) hsep2
  have hminor := (himp hunit).1
  have hoff : ∀ i j, i ≠ j → (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i j ∈ maximalIdeal 𝔞.V := by
    intro i j hij
    have h := hcg g0 i j
    rwa [Matrix.diagonal_apply_ne _ hij, sub_zero] at h
  have hdiff : ∀ i j, i ≠ j → IsUnit ((adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i i -
      (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) j j) := by
    intro i j hij
    apply unit_of_sub_mem (𝔞.unit_sub (hsep i j hij))
    have h1 := hcg g0 i i
    have h2 := hcg g0 j j
    simp only [Matrix.diagonal_apply_eq] at h1 h2
    have h3 := (maximalIdeal 𝔞.V).sub_mem h1 h2
    rw [sub_sub_sub_comm] at h3
    exact h3
  obtain ⟨P, v, b, hsm, hv, hv1, hPr, hdg, hlow, hb, hbup, hfac⟩ := Lab.exNorm 𝔞 (G ℚ Ω) r u pr g0
    (𝔞.a c ((D.th g0 : (c.O)ˣ) : c.O)) hK.small (𝔞.unit_two c hD.l_odd) ((D.th g0).isUnit.map _)
    (hK.mult g0) hK.sp _ _ rfl rfl hoff hdiff hunit hminor
  obtain ⟨hQ, hN⟩ := Lab.pairOf D hD 𝔞 r u hK pr g0 P v b hok hsm hv hv1 hPr hdg hlow hb hbup hfac
  have hm : IsGSp 1 (wM 𝔞.V pr * v) := sp_mul (wM_sp pr) hv
  have hinj : Function.Injective 𝔞.toK := fun x y h => Subtype.ext h
  have hmap : ∀ g, mapRep 𝔞.toK P.r g =
      adj ((wM 𝔞.V pr * v).map 𝔞.toK) * mapRep 𝔞.toK r g * (wM 𝔞.V pr * v).map 𝔞.toK := by
    intro g
    rw [mapRep_eq, mapRep_eq, hPr g, adj_map, Matrix.map_mul, Matrix.map_mul]
  have hparM : (∀ g, Par (mapRep 𝔞.toK r g)) → Par ((wM 𝔞.V pr * v).map 𝔞.toK) := by
    intro hp
    have hpr : Par (r g0) := fun i j hij => hinj (by
      have h := hp g0 i j hij
      rw [mapRep_eq, Matrix.map_apply] at h
      rw [h, map_zero])
    have hX : Par (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) :=
      Par.mul (Par.mul (Par.adj (wM_par pr)) hpr) (wM_par pr)
    have hXv : (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) * v = v * Matrix.diagonal (P.r g0).diag := by
      rw [hdg.diagonal_diag, hPr g0, adj_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc v (adj v), sp_mul_adj hv, Matrix.one_mul]
    have hpv : Par v := Lab.parEig 𝔞.V _ v _ hoff hdiff hv1 hXv hX
    have hpm := Par.mul (wM_par pr) hpv
    intro i j hij
    rw [Matrix.map_apply, hpm i j hij, map_zero]
  refine ⟨P, hQ, hN, ?_, ?_⟩
  · refine ⟨⟨(adj (wM 𝔞.V pr * v)).map 𝔞.toK, (wM 𝔞.V pr * v).map 𝔞.toK, ?_, ?_⟩, fun g => ?_⟩
    · rw [← Matrix.map_mul, sp_adj_mul hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [← Matrix.map_mul, sp_mul_adj hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hmap g, adj_map]
      rfl
  · intro hstar
    have hgm : IsGSp 1 ((wM 𝔞.V pr * v).map 𝔞.toK) := by
      simpa using gsp_map 𝔞.toK hm
    obtain ⟨h1, h2, h3⟩ := Lab.starConj 𝔞.K (G ℚ Ω) (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r)
      ((wM 𝔞.V pr * v).map 𝔞.toK) hgm hmap hparM hstar
    refine ⟨ent_of_map _ h1, ent_of_map _ h2, ?_⟩
    rcases h3 with h | h | h
    · exact Or.inl (ent_of_map _ h)
    · exact Or.inr (Or.inl (ent_of_map _ h))
    · exact Or.inr (Or.inr (ent_of_map _ h))
end
