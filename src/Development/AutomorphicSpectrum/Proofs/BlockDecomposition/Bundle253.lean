module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle238
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle237
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.LocalFields.Bundle001
import GroundTheory.LocalFields.FormalGroups.Bundle001
import GroundTheory.PAdicHodge.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisTerm

section Lin

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem stab_diag_mul {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (g : Matrix ι ι R) i i * ((g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by
  have h : ((g * g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h
  · exact h
  · intro b _ hb
    rw [(hg b (by simpa using hb) i rfl).2, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ i) h'

theorem det_uniq {n R : Type} [CommRing R] [Unique n] [DecidableEq n] (F : Fintype n) (A : Matrix n n R) :
    @Matrix.det n _ F R _ A = A default default :=
  Matrix.det_unique A

theorem bdet_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((bdet ({i} : Set ι) g : Rˣ) : R) = (g : Matrix ι ι R) i i := by
  classical
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, det_uniq]; rfl
  · refine absurd ?_ h
    rw [det_uniq]
    exact IsUnit.of_mul_eq_one _ (stab_diag_mul hg)

theorem bdet_inv_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) = ((g⁻¹ : GL ι R) : Matrix ι ι R) i i :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_singleton hg]; exact stab_diag_mul hg)

theorem inv_mulVec_single {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((g⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ Pi.single i 1 =
      (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) • (Pi.single i 1 : ι → R) := by
  funext r
  rw [Matrix.mulVec_single_one, bdet_inv_singleton hg]
  by_cases h : r = i
  · subst h; simp
  · have := (hg r (by simpa using h) i rfl).2
    rw [Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]
    exact this

end Lin

section ZetaNonvanishing₂

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem modPow_eq_exp (x : IdeleGroup k) (s : ℂ) :
    modPow x s = Complex.exp (s * ((adStd k).lg x : ℝ)) := by
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  have hne : ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  rw [modPow, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, mul_comm]
  rfl

theorem modPow_inv_neg (x : IdeleGroup k) (s : ℂ) : modPow x⁻¹ (-s) = modPow x s := by
  have h1 : modPow x⁻¹ (-s) * modPow x (-s) = 1 := by
    rw [← modPow_mul, inv_mul_cancel, modPow_one]
  have h2 : modPow x (-s) * modPow x s = 1 := by
    rw [← modPow_add, neg_add_cancel]; simp [modPow]
  calc modPow x⁻¹ (-s) = modPow x⁻¹ (-s) * (modPow x (-s) * modPow x s) := by rw [h2, mul_one]
    _ = modPow x s := by rw [← mul_assoc, h1, one_mul]

theorem lineZeta_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s ((u : 𝔸[k]) • v) =
      (((ω.toIdele u)⁻¹ : Circle) : ℂ) * modPow u (-s) * lineZeta Ψ ω s v := by
  have h := globalZeta_mul_right (fun t : 𝔸[k] => Ψ (t • v)) ω s u
  simp only [lineZeta, smul_smul, mul_comm] at h ⊢
  simpa only [mul_comm] using h

theorem lineZeta_inv_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (((u⁻¹ : IdeleGroup k) : 𝔸[k]) • v) =
      (ω.toIdele u : ℂ) * modPow u s * lineZeta Ψ ω s v := by
  rw [lineZeta_smul, modPow_inv_neg, map_inv, inv_inv]

theorem lineZeta_rat (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (x : kˣ)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (algebraMap k 𝔸[k] x • v) = lineZeta Ψ ω s v := by
  have h := lineZeta_smul Ψ ω s (IdeleGroup.diagonal k x) v
  rw [IdeleGroup.coe_diagonal] at h
  rw [h, HeckeCharacter.toIdele_diagonal]
  simp [modPow, IdeleGroup.ideleModule_diagonal]

end ZetaNonvanishing₂

section Main

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_inv_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem dgl_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (d i : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (d i : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem vec_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {p : G} (κ : G)
    (hp : π p ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (π (p * κ) * dgl d) i =
      (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hinv : (π (p * κ) * dgl d)⁻¹ = (kap π d κ)⁻¹ * ((dgl d)⁻¹ * (π p)⁻¹) := by
    simp only [kap, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  have hs : (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) * (((bdet ({i} : Set ι) (π p))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev]
  unfold MG.vec
  rw [hinv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    inv_mulVec_single hp, Matrix.mulVec_smul, dgl_inv_mulVec_single, smul_smul, Matrix.mulVec_smul, hs,
    mul_comm]

theorem vec_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    MG.vec (kap π d g) i = (d i : 𝔸[k]) • MG.vec (π g * dgl d) i := by
  have hinv : (kap π d g)⁻¹ = (π g * dgl d)⁻¹ * dgl d := by
    simp only [kap, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  unfold MG.vec
  rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec, dgl_mulVec_single, Matrix.mulVec_smul]

theorem vec_kap_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {r : G} (κ : G)
    (hr : π r ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (kap π d (r * κ)) i =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hs : (d i : 𝔸[k]) * (((bdet ({i} : Set ι) (π r) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, mul_comm (d i)⁻¹, mul_inv_cancel_comm_assoc]
  rw [vec_kap, vec_mul π d i κ hr, smul_smul, hs]

end Main

theorem term : Term := by
  intro G _ _ _ _ K _ k _ _ ι _ _ π Γ P i ω d c η S
  have hmem : ∀ p ∈ P, π p ∈ stab 𝔸[k] ({i} : Set ι) := fun p hp => (S.mem p).1 hp
  refine ⟨fun p hp κ _ => vec_mul π d i κ (hmem p hp), fun Ψ s => ⟨?_, ?_, fun x v => lineZeta_rat Ψ ω s x v⟩⟩
  · intro p hp κ _
    have hc := (S.val p hp).1
    have hη := (S.val p hp).2
    rw [vec_mul π d i κ (hmem p hp), lineZeta_inv_smul, map_mul, Circle.coe_mul, modPow_mul,
      modPow_eq_exp (bdet ({i} : Set ι) (π p)) s, hc, hη]
    simp only [zt]
    ring
  · intro r κ hr
    have hc := (S.val r hr).1
    have hη := (S.val r hr).2
    have h0 : η r = 0 := by
      have h1 := S.ht.right 1 r r.2
      have h2 := S.ht.left r hr 1
      rw [one_mul] at h1
      rw [mul_one] at h2
      linarith
    have hm : modPow (bdet ({i} : Set ι) (π r)) s = 1 := by
      rw [modPow_eq_exp, ← hη, h0]; simp
    show zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ
    rw [Subgroup.coe_mul]
    simp only [zt]
    rw [vec_kap_mul π d i κ ((S.mem r).1 hr), lineZeta_inv_smul, hm, hc, mul_one]

end GlobalTheory.CompanionTheory.RgEisTerm
end
end

section

noncomputable section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMir

theorem avg_one_apply {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (ρ : K →* (W →L[ℂ] W)) (hρ : Continuous ρ) (w : W)
    (hw : ∀ r : K, ρ r w = w) : avg μ ρ (fun _ => (1 : ℂ)) w = w := by
  have hint : Integrable (fun κ : K => (1 : ℂ) • ρ κ) μ := by
    simp only [one_smul]
    exact hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [avg]
  rw [ContinuousLinearMap.integral_apply hint]
  simp [hw]

theorem isPar_top {G : Type} [Group G] [TopologicalSpace G] (Γ K : Subgroup G) :
    IsPar Γ K ⊤ (1 : G → ℂ) := by
  refine ⟨?_, fun g => ⟨g, Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩, ?_⟩
  · simp only [Subgroup.coe_top]
    exact isClosed_univ
  · exact ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp,
      continuous_const.continuousOn⟩

theorem sec_top_apply {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) (g : G) (w : W)
    (hw : ∀ r : K, ρ r w = w) : sec K ⊤ (1 : G → ℂ) ρ g w = w := by
  unfold sec
  rw [dite_eq_left ⟨1, Subgroup.mem_top _⟩]
  simp [hw]

theorem mirGen_of_core : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  intro _hSec hSph hMem hInv hSide hTK hCore G _ _ _ _ _ W _ _ _ K ρ hK hρ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hSC hMD
  haveI := hSC
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  have hHaar : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hProb : IsProbabilityMeasure μ := ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using h⟩
  haveI := hProb
  have hN1 : (1 : ℝ) < Fintype.card ι := by
    have h2 := hMD.two
    exact_mod_cast (show 1 < Fintype.card ι by omega)
  obtain ⟨hS0, -, -, -⟩ := hSide G K hK k ι π Γ i₀ i₁ ω d c η η' l hMD
  obtain ⟨V, hV, hJV⟩ := hInv G W K ρ hK hρ μ hHaar hProb Γ _ c hMD.par
  obtain ⟨Ψ, Ψ₁, φ, hΨ, hΨ₁, hφc, hφ1, hφL, hφN, hzt, hz, hω1⟩ :=
    hTK G K hK k ι π Γ _ i₀ ω d c η hS0 V hV
  obtain ⟨J, hJ⟩ := hJV φ hφc hφ1 hφL hφN
  obtain ⟨R, D, Op, H, hW, ⟨dd, hdd, hD, hddN⟩, -, hH⟩ :=
    hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ ω d c η η' l hMD Ψ Ψ₁ φ _ J hΨ hΨ₁ hzt hz le_rfl hJ
  refine ⟨⟨R, D, Op, H, hW⟩, fun hω hc => ?_⟩
  subst hω
  subst hc
  have hinv : ∀ w ∈ secSp K ⊤ (1 : G → ℂ) ρ, ∀ r : K, ρ r w = w := fun w hw r => by
    simpa using hw r (Subgroup.mem_top _)
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψs, Ψ₁s, hΨs, hΨ₁s, hΨ0, hsph, hnz⟩ := hSph k ι i₀
    have hzt' : ∀ s (κ : K), zt π d i₀ Ψs 1 s κ = tate Ψ₁s 1 s * (fun _ => (1 : ℂ)) κ := by
      intro s κ
      simp only [mul_one]
      unfold zt tate lineZeta
      congr 1
      funext t
      exact hsph t ⟨kap π d κ, hS0.piK κ κ.2⟩
    have hnz' : ∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁s 1 z ≠ 0 :=
      ⟨(((Fintype.card ι : ℝ) + 1 : ℝ) : ℂ), by simp, hnz _ (by linarith)⟩
    have hle : secSp K ⊤ (1 : G → ℂ) ρ ≤ secSp K ((stab _ {i₀}).comap π) 1 ρ :=
      fun w hw r _ => hw r (Subgroup.mem_top _)
    have havg : ∀ w : secSp K ⊤ (1 : G → ℂ) ρ,
        avg μ ρ (fun _ => (1 : ℂ)) ((secSp K ⊤ (1 : G → ℂ) ρ).subtypeL w) = w := fun w => by
      simpa using avg_one_apply μ ρ hρ (w : W) (hinv w w.2)
    obtain ⟨R', D', Op', H', hW', -, ⟨O', hO', hOp'⟩, hH'⟩ :=
      hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ 1 d 1 η η' l hMD Ψs Ψ₁s (fun _ => 1)
        (secSp K ⊤ (1 : G → ℂ) ρ) (secSp K ⊤ (1 : G → ℂ) ρ).subtypeL hΨs hΨ₁s hzt' hnz' hle havg
    obtain ⟨⟨a, ha, hH0⟩, -⟩ := hH' rfl
    refine ⟨R', D', Op', H', hW', ⟨a, ha, fun g w => ?_⟩, O', hO', hOp'⟩
    rw [hH0, hΨ0, mul_one, havg w, sec_top_apply K ρ g (w : W) (hinv w w.2)]
  · obtain ⟨-, b, hb⟩ := hH rfl
    have hmem : ∀ v, avg μ ρ (fun _ => (1 : ℂ)) v ∈ secSp K ⊤ (1 : G → ℂ) ρ :=
      hMem G W K ρ hK hρ μ hHaar hProb Γ ⊤ 1 (isPar_top Γ K) (fun _ => 1) continuous_const
        (fun _ _ _ => by simp)
    let T : secSp K ((stab _ {i₀}).comap π) 1 ρ →L[ℂ] secSp K ⊤ (1 : G → ℂ) ρ :=
      b • ((avg μ ρ (fun _ => (1 : ℂ))).comp J).codRestrict _ (fun w => hmem (J w))
    refine ⟨R, D, Op, H, hW, ⟨dd, hdd, hddN (hω1 rfl _ hN1), hD⟩, T, fun g w => ?_⟩
    rw [hb g w, sec_top_apply K ρ g _ (hinv _ (T w).2), mul_smul]
    rfl

end GlobalTheory.CompanionTheory.EisMir
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inv_mulVec_smul_vec (m γ : GL ι 𝔸[k]) (x : 𝔸[k]) (i : ι) :
    ((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ (x • MG.vec γ i) = x • MG.vec (γ * m) i := by
  unfold MG.vec
  rw [Matrix.mulVec_smul, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]


omit [Fintype ι] [DecidableEq ι] in
theorem norm_lineZeta_le (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (v : ι → 𝔸[k]) :
    ‖lineZeta Ψ ω s v‖ ≤ ∫ t : IdeleGroup k, ‖Ψ ((t : 𝔸[k]) • v)‖ *
      (IdeleGroup.ideleModule k t : ℝ) ^ s.re ∂ideleMeasure k := by
  unfold lineZeta globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k t : ℝ) := (IdeleGroup.ideleModule k t).2
  simp only [norm_mul, Circle.norm_coe, mul_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]

section Eis

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (φ : K → ℂ) :
    avg μ ρ (fun κ => a * φ κ) = a • avg μ ρ φ := by
  unfold avg
  rw [← integral_smul]
  simp only [smul_smul]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => by rw [map_smul, smul_comm]

end Eis

theorem sideUnfold : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  intro hE hU hL hT hZ G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ s hs g w
  have hcard : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    have := hS.two
    exact_mod_cast (by omega : 1 < Fintype.card ι)
  have hs1 : 1 < s.re := hcard.trans hs
  obtain ⟨e, he⟩ := hL G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hT1, hT2⟩ := hT G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hTp, hTl, hTx⟩ := hT2 Ψ s
  obtain ⟨-, hZc, -⟩ := hZ G K hK k ι π Γ P i ω d c η hS Ψ hΨ
  set a : ℂ := (ω.toIdele (d i) : ℂ) * modPow (d i) s with ha
  let T : G → ℂ := fun y => lineZeta Ψ ω s (MG.vec (π y * dgl d) i)
  let φ : K → ℂ := fun κ => a * zt π d i Ψ ω s κ
  let Λ : G → ℂ := fun x => s * η x
  have key : ∀ (y : G) (q : Cos P Γ), lineZeta Ψ ω s
      (((π y * dgl d)⁻¹ : GL ι 𝔸[k]).1 *ᵥ ratV (e q).rep) = T (rep q * y) := by
    intro y q
    obtain ⟨x, hx⟩ := he q
    rw [hx, inv_mulVec_smul_vec, hTx]
    simp only [T, map_mul, mul_assoc]
  have hφc : Continuous φ := by
    have h1 : Continuous fun κ : K => zt π d i Ψ ω s κ := by
      have h2 : ContinuousOn (fun y : ℂ × K => zt π d i Ψ ω y.1 y.2) (Set.univ.image fun κ : K => (s, κ)) :=
        hZc.mono (by rintro _ ⟨κ, -, rfl⟩; exact ⟨hs1, Set.mem_univ _⟩)
      have h3 := h2.comp_continuous (f := fun κ : K => (s, κ)) (by fun_prop) (fun κ => ⟨κ, Set.mem_univ _, rfl⟩)
      exact h3
    exact continuous_const.mul h1
  have hφl : Law K P c φ := fun r κ hr => by
    have h : zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ := hTl r κ hr
    simp only [φ]
    rw [h]
    ring
  have hΛ : ∀ x, ∀ κ ∈ K, Λ (x * κ) = Λ x := fun x κ hκ => by
    simp only [Λ, hS.ht.right x κ hκ]
  have hTP : ∀ p ∈ P, ∀ κ : K, T (p * κ) = c p * Complex.exp (Λ p) * φ κ := fun p hp κ =>
    hTp p hp κ κ.2
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hCc : IsCompact (Set.range fun κ : K => ((π (g * κ) * dgl d)⁻¹ : GL ι 𝔸[k])) := by
    refine isCompact_range ?_
    have hπ := hS.cont
    exact ((hπ.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const).inv
  obtain ⟨u, hu, hub⟩ := (hE k ι Ψ hΨ).2 s.re _ (max_lt hs1 hs |>.trans_le le_rfl) hCc
  have hbound : ∀ (q : Cos P Γ) (κ : K), ‖T (rep q * (g * κ))‖ ≤ (u ∘ e) q := fun q κ => by
    rw [← key]
    exact (norm_lineZeta_le Ψ ω s _).trans (hub _ ⟨κ, rfl⟩ (e q))
  have hfun : (fun κ : K => epstein Ψ ω s (π (g * κ) * dgl d)) = fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ)) := by
    funext κ
    unfold epstein
    rw [← e.tsum_eq]
    exact tsum_congr fun q => key _ q
  have hmain := hU G W K ρ hK hρ μ hμ hP Γ P c hS.par φ Λ T hφc hφl hΛ hTP g (u ∘ e) (e.summable_iff.2 hu) hbound w
  rw [hfun, hmain]
  simp only [φ]
  rw [avg_const_mul, _root_.smul_apply, eis_smul]

end GlobalTheory.CompanionTheory.RgEisSide
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.local_embedding_range_eq_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | exact GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | (intros; apply GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw <;> assumption)
end
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.bernstein_zelevinsky_geometric_lemma : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  first | exact @GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | exact GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | (intros; apply GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.finiteDimensional_chart_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ), IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  first | exact @GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | exact GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | (intros; apply GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ <;> assumption)
end
