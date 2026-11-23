module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle115
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle006
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

open scoped Pointwise

theorem res_T_indep (D : D7) (a : D.nd.Loc) (f : D.nd.T a) (x x' : D.nd.X a) :
    IsLocalRing.residue (D.nd.O a) ((f : D.nd.X a → D.nd.O a) x) =
      IsLocalRing.residue (D.nd.O a) ((f : D.nd.X a → D.nd.O a) x') := by
  have := D.nd.T_local a
  let ev : D.nd.X a → (D.nd.T a →+* IsLocalRing.ResidueField (D.nd.O a)) := fun y =>
    (IsLocalRing.residue (D.nd.O a)).comp
      ((Pi.evalRingHom (fun _ : D.nd.X a => D.nd.O a) y).comp (D.nd.T a).val.toRingHom)
  have hsurj : ∀ y, Function.Surjective (ev y) := by
    intro y c
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
    exact ⟨algebraMap (D.nd.O a) (D.nd.T a) c', rfl⟩
  have hker : ∀ y, RingHom.ker (ev y) = IsLocalRing.maximalIdeal (D.nd.T a) := fun y =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev y) (hsurj y))
  have h1 : f - algebraMap (D.nd.O a) (D.nd.T a) ((f : D.nd.X a → D.nd.O a) x) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, (ev x).map_sub]
    exact sub_self _
  rw [hker x, ← hker x', RingHom.mem_ker, (ev x').map_sub, sub_eq_zero] at h1
  exact h1.symm

theorem heckePol_res (D : D7) (a : D.nd.Loc) (x x' : D.nd.X a) (w : PlE D.host) :
    (heckePol D.nd a x w).map (IsLocalRing.residue (D.nd.O a)) =
      (heckePol D.nd a x' w).map (IsLocalRing.residue (D.nd.O a)) := by
  unfold heckePol

  simp only [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
  Polynomial.map_mul, Polynomial.map_C, map_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [res_T_indep D a (D.nd.hT a w k) x x']

theorem isOpen_res_fiber (D : D7) (a : D.nd.Loc) (c : IsLocalRing.ResidueField (D.nd.O a)) :
    IsOpen {y : D.nd.O a | IsLocalRing.residue (D.nd.O a) y = c} := by
  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal _) : Set (D.nd.O a)) := by
    have := (isAdic_iff.mp (D.nd.O_adic a)).1 1
    rwa [pow_one] at this
  rw [isOpen_iff_mem_nhds]
  intro y0 hy0
  have hc : Continuous fun y : D.nd.O a => y - y0 := continuous_id.sub continuous_const
  have hU := (hm.preimage hc).mem_nhds (x := y0) (by simp)
  refine Filter.mem_of_superset hU fun y hy => ?_
  have : IsLocalRing.residue (D.nd.O a) (y - y0) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hy
  rw [map_sub, sub_eq_zero] at this
  exact this.trans hy0

section Defs

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsRhoOf (a : N.Loc) (x : N.X a) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O a)) : Matrix (Fin R.r) (Fin R.r) (N.O a))) ∧
  IsSSRep (mapRep (algebraMap (N.O a) (Kf N a)) ρ) ∧
  ∀ w, SplitOut N a w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly *
      ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi a c σ : (N.O a)ˣ) : N.O a)) = heckePol N a x w

end Defs

def ResidualIrreducibleRankR (D : D7) : Prop :=
  ∀ a, HG D.nd D.naut a → ∀ rb, IsRhoBar D.nd a rb →
    Formalism.CyclotomicNorms.IrredOn (mapRep (D.naut.kFbar a) rb) ⊤ ∧
    ∀ k, D.nd.l a ≠ D.host.g k → ∀ v ∈ placesOver D.host.E (D.host.g k),
      ¬ (((rb (D.nd.gam0 a v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (D.nd.O a) (chi1 D.nd a (D.nd.gam0 a v)))

def LitBurnside (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)), Formalism.CyclotomicNorms.IrredOn ρ ⊤ →
    Submodule.span (Formalism.CyclotomicNorms.Fbar ℓ)
      (Set.range fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ))) = ⊤

theorem isRhoBar_of_isRhoOf (D : D7) (a : D.nd.Loc) (x : D.nd.X a)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O a)) (h : IsRhoOf D.nd a x ρ) :
    IsRhoBar D.nd a (redRep D.nd a ρ) := by
  refine ⟨?_, ?_⟩
  · have e : ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) =
        (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ⁻¹'
          (⋂ p : Fin D.R.r × Fin D.R.r, {M | IsLocalRing.residue (D.nd.O a) (M p.1 p.2) =
            (1 : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) p.1 p.2}) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_iInter,
        Set.mem_ofPred_eq, Prod.forall]
      constructor
      · intro hg i j
        have := congrArg (fun u : GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a)) =>
          u.val i j) hg
        exact this
      · intro hg
        apply Units.ext
        ext i j
        exact hg i j
    rw [e]
    refine IsOpen.preimage h.1 (isOpen_iInter_of_finite fun p => ?_)
    have hc : Continuous fun M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) => M p.1 p.2 :=
      continuous_id.matrix_elem p.1 p.2
    exact (isOpen_res_fiber D a _).preimage hc
  · intro x' w hw B σ hB hσ
    rw [← heckePol_res D a x x' w, ← h.2.2 w hw B σ hB hσ, Polynomial.map_mul, Polynomial.map_prod]
    congr 1
    · exact Matrix.charpoly_map _ _
    · refine Finset.prod_congr rfl fun c _ => ?_
      simp

theorem span_descent {k L : Type} [Field k] [Field L] (φ : k →+* L) {n : ℕ} {ι : Type}
    (S : ι → Matrix (Fin n) (Fin n) k)
    (h : Submodule.span L (Set.range fun i => (S i).map φ) = ⊤) :
    Submodule.span k (Set.range S) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let c : Fin n → Fin n → k := fun i j => f (Matrix.single i j 1)
  have hfc : ∀ M : Matrix (Fin n) (Fin n) k, f M = ∑ i, ∑ j, M i j * c i j := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  let F : Matrix (Fin n) (Fin n) L →ₗ[L] L :=
    ∑ i, ∑ j, (φ (c i j)) • Matrix.entryLinearMap L L i j
  have hF : ∀ M : Matrix (Fin n) (Fin n) L, F M = ∑ i, ∑ j, φ (c i j) * M i j := by
    intro M
    simp [F, LinearMap.sum_apply]
  have hker : Submodule.span L (Set.range fun i => (S i).map φ) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h0 : f (S i) = 0 := hf (Submodule.subset_span ⟨i, rfl⟩)
    rw [hfc] at h0
    show F ((S i).map φ) = 0
    rw [hF]
    have := congrArg φ h0

    simp only [map_sum, map_mul, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.map_apply, mul_comm]
  rw [h, top_le_iff, LinearMap.ker_eq_top] at hker
  apply hf0
  apply LinearMap.ext
  intro M
  rw [hfc]
  have hc : ∀ i j, c i j = 0 := by
    intro i j
    have := hF (Matrix.single i j 1)
    rw [hker, LinearMap.zero_apply] at this
    have h2 : ∑ p, ∑ q, φ (c p q) * (Matrix.single i j (1 : L)) p q = φ (c i j) := by
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp
      · intro q _ hq
        simp [Matrix.single_apply, Ne.symm hq]
      · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        simp [Matrix.single_apply, Ne.symm hp]
      · simp
    rw [h2] at this
    exact (map_eq_zero_iff φ φ.injective).mp this.symm
  simp [hc]

theorem conj_mem_Ine_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (τ σ : G F Ω) (hσ : σ ∈ Ine (F := F) A) :
    τ * σ * τ⁻¹ ∈ Ine (F := F) (τ • A) := by
  apply GlobalTheory.TameMove.conj_mem_Ine_smul <;> assumption

theorem placesOver_disj (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (v : HeightOneSpectrum (𝓞 E)) (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h1' : ((p : ℤ) : 𝓞 E) ∈ v.asIdeal := by
    have : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
    simpa using this
  have h2' : ((q : ℤ) : 𝓞 E) ∈ v.asIdeal := by
    have : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
    simpa using this
  have hb : (1 : 𝓞 E) ∈ v.asIdeal := by
    have hg := Nat.gcd_eq_gcd_ab p q
    rw [hco.gcd_eq_one] at hg
    have : (1 : 𝓞 E) = ((p : ℤ) : 𝓞 E) * ((Nat.gcdA p q : ℤ) : 𝓞 E) + ((q : ℤ) : 𝓞 E) * ((Nat.gcdB p q : ℤ) : 𝓞 E) := by
      have := congrArg (fun z : ℤ => (z : 𝓞 E)) hg
      push_cast at this
      simpa using this
    rw [this]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1') (v.asIdeal.mul_mem_right _ h2')
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hb)

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Glue

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

def coreB (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
    (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)

end Glue

section Row

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)

abbrev LatW : Type 1 := LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥Cx.LL.1 ↥(OL Cx.LL)

def IsTwistedDualOfGaloisRep (T₂ : LatW i w hw Cx) : Prop :=
  IsMatLat (ρ := T₂.ρ) T₂.L.T ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))

def IsSubOfTwistedDualSums (T₁ : LatW i w hw Cx) : Prop :=
  IsSubOfSums T₁.ρ (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)))

def RowL (x : ℝ) : Prop :=
  ∀ (T₁ T₂ : LatW i w hw Cx) (F : LatHom T₁.L T₂.L), IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → IsSubOfTwistedDualSums i r w hw Cx T₁ →
    F.Onto → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR (Br.PD D.loc D.nbr i w hw) F x

abbrev nLet : ℕ := finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)

theorem nLet_neZero : NeZero (nLet i w hw) := by
  have := (D.nbr i w hw).Kw.2
  have h0 : K0 (D.nbr i w hw).Kw ≤ (D.nbr i w hw).Kw.1 := inf_le_left
  have : FiniteDimensional ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) :=
    Module.Finite.of_injective (IntermediateField.inclusion h0).toLinearMap
      (IntermediateField.inclusion h0).injective
  exact ⟨(finrank_pos).ne'⟩

end Row

structure WordDat (n : ℕ) where
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  up : ZMod n → Bool
  sz : ZMod n → ℕ
  Mi : ZMod n → ℕ
  hi : ZMod n → ℕ

def WordDat.win {n : ℕ} (Wd : WordDat n) (a : ZMod n) : Set ℤ :=
  if Wd.up a then Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
  else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η

section Word

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

abbrev WW := (HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG

structure WordBase (Wd : WordDat (nLet i w hw)) : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (K := ↥(D.nbr i w hw).Kw.1) (Qp := ℚ_[D.nd.l i]) ↥Cx.LL.1
  dvr : ∃ hO : IsDomain ↥(OL Cx.LL), @IsDiscreteValuationRing ↥(OL Cx.LL) _ hO ∧
    IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1
  t1 : ∀ T₁ : LatW i w hw Cx, IsSubOfTwistedDualSums i r w hw Cx T₁ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧
    Formalism.MainNotions.LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi
  t2 : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a : ZMod (nLet i w hw)),
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ Wd.m
  thick_or : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∨ Wd.sz a ≤ Wd.w
  h_le : (Wd.b : ℝ) + Wd.η + Wd.S ≤ Formalism.MainNotions.TwistedPlaces.hB L
  w_le : (Wd.w : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.wP L
  S_le : (Wd.S : ℝ) ≤ L.Sc
  η_le : (Wd.η : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eta₃ L
  m_eq : Wd.m = D.R.m

variable {L HW i r ρ π w hw Cx hG}

structure WordsB (L : SizeData₂ D) (C₂ : ℝ) (l : ℕ) {n : ℕ} (Wd : WordDat n) : Prop where
  j_lt : Formalism.MainNotions.TwistedPlaces.jA L l + 1 ≤ n
  par : C₂ * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ Wd.b
  clusters : Formalism.MainNotions.TruncatedSeriesCountingBounds.Clusters (Formalism.MainNotions.TwistedPlaces.jA L l) (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)

end Word

def ratIn (x y : ℝ) : ℚ := if h : x < y then (exists_rat_btwn h).choose else 0

section RowB

variable (L : SizeData₂ D)

def lenRowB (C₂ : ℝ) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (3 * C₂ * coreB L l lam) ((3 * C₂ + 1) * coreB L l lam)

def LocalRepresentationBoundCondition (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordsB L C₂ (D.nd.l i) Wd

end RowB

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

variable (D : D7) {Dall Dgood : ℕ}

def CountCylAt (A : AllRowsAt D Dall Dgood) (c₃ : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    |(A.dimT (cyl D k S) : ℝ) -
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))

end Formalism.MainNotions.N.CylinderCountFamily
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

end Formalism.MainNotions.N
end
end
