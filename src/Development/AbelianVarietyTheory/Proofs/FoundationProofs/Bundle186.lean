module

public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.GradedWeylDivisibility.Bundle001
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
public import Formalism.LocalRingCardinality.DataDIV
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle176
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory.WeylInt

open Formalism.GradedWeylDivisibility

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  have key : ∀ (k : ℕ) (hk : k < n) (a : Fin r), a.val < k → m (a, ⟨k, hk⟩) = 0 := by
    intro k
    induction k with
    | zero => intro hk a ha; omega
    | succ k ih =>
      intro hk a ha
      have h1 := h ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl a
      have h2 : (∑ b : Fin r with b < a, m (b, ⟨k, by omega⟩)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ih _ b ?_
        have : b.val < a.val := (Finset.mem_filter.mp hb).2
        omega
      rw [h2] at h1
      have h3 : m (a, ⟨k + 1, hk⟩) ≤ ∑ b : Fin r with b ≤ a, m (b, ⟨k + 1, hk⟩) :=
        Finset.single_le_sum (f := fun b : Fin r => m (b, ⟨k + 1, hk⟩)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)
      omega
  intro a s has
  exact key s.val s.2 a has

theorem intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl

theorem intQ_bidet {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    intQ r n (bideterminant ℤ sz hsz I) = bideterminant ℚ sz hsz I := by
  rw [intQ_apply]
  simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext1 i j
  simp

theorem lowerTriIntegral : Formalism.GradedWeylDivisibility.LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl ℚ r n ν,
      (colLex r n).toSyn ((colLex r n).degree f) = d →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff f e = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f = intQ r n Q' by
    intro f hf hint
    exact key _ f hf rfl hint
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hd hz
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hdeg, hlc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rwa [hshape] at this
    obtain ⟨z, hzm⟩ := hz m (lowerTri_of_interlaced hint)
    have hlcf : (colLex r n).leadingCoeff f = (z : ℚ) := hzm
    set f' := f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I with hf'
    have hf'mem : f' ∈ dualWeyl ℚ r n ν := Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hmem)
    have hb : (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [map_smul, intQ_bidet, hlcf, Int.cast_smul_eq_zsmul]
    have hdecomp : f = f' + intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [hf', ← hb]; abel
    have hQ : ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f' = intQ r n Q' := by
      by_cases h0 : f' = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hdeg.trans hexp) hlc h0
      refine ih _ (hd ▸ hlt) f' hf'mem rfl fun e he => ?_
      obtain ⟨w, hw⟩ := hz e he
      refine ⟨w - AddMonoidAlgebra.coeff (z • bideterminant ℤ sz hsz I) e, ?_⟩
      rw [hf', hb, MvPolynomial.coeff_sub, hw, intQ_apply, coeff_map]
      simp only [Int.cast_sub, eq_intCast]
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨Q' + z • bideterminant ℤ sz hsz I, by rw [map_add (f := _), ← hQ']; exact hdecomp⟩

end GlobalTheory.WeylInt
end

section

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory

def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ) (hj : 1 ≤ j)
    (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := lev
  lev_prime := hlev
  Comp := Unit
  vol := 0
  chern := 0
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl
  CurveHT := fun _ => Empty
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty
  fibInBd := fun _ _ => False
  Pt := Unit
  phiDR := fun _ _ _ => 0
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 0
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_rfl⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  compOf := fun _ => ()
  normDetInf := fun _ _ => 1
  compPt := fun _ => ()
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  ALB := Unit
  arSelf := fun _ => 0
  arSelfC := fun _ _ => 0
  arSelf_sum := fun _ => by simp
  geo := fun _ => 0
  geoC := fun _ _ => 0
  geo_sum := fun _ => by simp
  arVol := fun _ => 0
  semipos := fun _ => True
  nefFib := fun _ => True
  arNef := fun _ => True
  Mbar := fun _ _ _ => ()

end GlobalTheory

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}


open Classical in
def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

@[simp] theorem AdelicLine.of_inf (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) :
    (AdelicLine.of a b).inf = a := by
  unfold AdelicLine.of; split_ifs <;> rfl

theorem AdelicLine.of_fin (a : InfinitePlace F → ℝ) {b : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : (Function.mulSupport b).Finite) : (AdelicLine.of a b).fin = b := by
  unfold AdelicLine.of; rw [dite_eq_left h]

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

theorem AdelicLine.twist_fin (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (h : (Function.support cf).Finite) :
    (L.twist ci cf).fin = fun w => Real.exp (-cf w) * L.fin w := by
  refine AdelicLine.of_fin _ ((h.union L.fin_finite).subset fun w hw => ?_)
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, Function.mem_mulSupport, not_or, not_not] at hn
  exact hw (by simp [hn.1, hn.2])

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  Eff _ _ := True
  eff_zero _ := trivial
  eff_add _ _ _ _ _ := trivial
  H0 _ _ := ⊤
  degreeZeroCohomology_finiteDimensional _ _ := inferInstance
  mul_mem_riemannRochSpace_add _ _ _ _ _ _ _ := Submodule.mem_top
  riemannRoch_mono _ _ _ _ := le_rfl
  KY _ := 0
  Cl _ := Set Unit
  properCl _ Z := Z ≠ Set.univ
  subCl _ Z Z' := Z ⊆ Z'
  supp _ _ := ∅
  inter _ _ := 1
  nef _ _ := True
  big _ _ := True
  bpf _ _ V := ∃ f ∈ V, f ≠ 0
  phiBir _ _ V := ∃ f ∈ V, f ≠ 0
  phiNoContr _ _ _ _ := True
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  hdim _ i _ := if i = 0 then 1 else 0
  pts _ _ := Unit
  ptsMeas _ _ := ⊤
  vol _ _ := @MeasureTheory.Measure.dirac Unit ⊤ ()
  FnC _ _ := ℂ
  cx _ σ := σ
  cx_smul _ σ a f := by simp
  Met _ _ _ := ℝ≥0
  mAdd _ _ _ _ h h' := h * h'
  mPow _ _ _ k h := h ^ k
  fsMet _ _ _ _ _ e := ∑ k, ‖e k‖₊ ^ 2
  pn _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  pnK _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  mSmooth _ _ _ h := h ≠ 0
  mPsh _ _ _ _ _ := True
  redZero _ _ _ _ S := S = Set.univ
  agreeOn _ _ _ f g S := S.Nonempty → f = g
  resNorm _ _ _ h _ _ _ g _ := ‖g‖ ^ 2 / (h : ℝ)
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg
  supInf _ L v τ f := v f * L.inf v ^ τ
  supFin _ L w τ f := FinitePlace.mk w f * L.fin w ^ τ
  cutGood _ bd _ _ _ _ _ _ _ := bd = ∅
  cutHt _ L _ _ _ _ _ _ _ := L.deg
  cutOrd _ _ _ _ _ _ _ _ _ _ := 0
  resFull _ _ _ _ _ _ _ _ M ι _ :=
    (M.L.map (ι.restrictScalars (𝓞 F))).FG ∧ M.L.map (ι.restrictScalars (𝓞 F)) ≠ ⊥
  resDeg _ _ _ _ _ _ _ _ M ι L := (AdelicLine.of L.inf (latticeNorm M ι)).deg
  supInf_ofW _ _ W ι v τ f := by
    rw [ciSup_unique]
    change v f * (ofLattice W ι).inf v ^ τ =
      Real.sqrt (‖v.embedding f‖ ^ 2 / ((frameSq W ι v ^ τ : ℝ≥0) : ℝ))
    rw [ofLattice, AdelicLine.of_inf, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      InfinitePlace.norm_embedding_eq, inv_pow, div_eq_mul_inv]
    congr 2
    rw [NNReal.coe_pow, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (NNReal.coe_nonneg _)]
  supInf_twist _ L ci cf _ v τ f := by
    rw [AdelicLine.twist, AdelicLine.of_inf, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  supFin_twist _ L ci cf h w τ f := by
    rw [AdelicLine.twist_fin L ci h, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  regOn _ _ _ _ _ := True

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
end
end

section

namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by

        rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
end

section

namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
end

section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeriesSummable_mul_divisorSum' : ∀ (e : ℕ) (ψ θ g b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n : ℕ => g n * b n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum | exact GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum | (intros; apply GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum <;> assumption)
end

section

namespace GlobalTheory

theorem padicInt_module_finite_of_separated_of_finite_quotient (l : ℕ) [Fact l.Prime] (X : Type)
    [AddCommGroup X] [Module ℤ_[l] X]
    (hfin : Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))))
    (hsep : ∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) :
    Module.Finite ℤ_[l] X := by
  have hI : IsLocalRing.maximalIdeal ℤ_[l] = Ideal.span {(l : ℤ_[l])} :=
    PadicInt.maximalIdeal_eq_span_p
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[l]) X := by
    refine ⟨fun x hx => hsep x fun r => ?_⟩
    have h := hx r
    rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy⟩
  have hE : (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X) =
      LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1)) := by
    ext x
    rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp [LinearMap.mem_range]
  have : Module.Finite ℤ_[l] (X ⧸ (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X)) := by
    rw [hE]
    exact Module.Finite.of_finite
  exact finite_of_isHausdorff_of_finite_quotient (IsLocalRing.maximalIdeal ℤ_[l]) X

end GlobalTheory
end
